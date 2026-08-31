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

## Cohen–Macaulay theory: the build has started

`Cohen–Macaulay` occurs nowhere in mathlib or in this corpus, so the last clause of the theorem
("every `C_k` is normal, Cohen–Macaulay, and has rational singularities") needs the theory built
from scratch.  Three modules are in, all axiom-clean and wired:

```text
HTGeometry/CohenMacaulayDepth.lean
    IsRegularOn, IsRingRegularSeq            regular sequences via ideal quotients
    ofList_nil, ofList_cons, ofList_map
    nonZeroDivisor_of_isRingRegularSeq_cons
    isRingRegularSeq_tail                    the tail is regular modulo the head
    ringKrullDim_quotient_bot
    ringKrullDim_quotient_ofList_add_length_le
        ** a regular sequence drops the Krull dimension by its length **
    length_le_ringKrullDim_of_isRingRegularSeq
    ringDepth, IsCohenMacaulayRing           depth, and depth = dimension
    IsCohenMacaulayRing.exists_maximal_regular

HTGeometry/PolynomialCohenMacaulay.lean
    ofList_map_X, isRegularOn_X_of_notMem
    getElem_notMem_take_of_nodup            (missing from mathlib)
    isRingRegularSeq_finRange_X
    isCohenMacaulayRing_mvPolynomial
        ** a polynomial ring over a field is Cohen–Macaulay **

HTGeometry/CohenMacaulayLifting.lean
    ofList_append, isRingRegularSeq_append   concatenation of regular sequences
    exists_list_map_mk
    isCohenMacaulayRing_of_quotient
        ** Cohen–Macaulayness lifts through a regular sequence **
```

### The route to the card's clause, decided

The `r = 1` stratum is within reach and its proof is settled.  `C_{m−1}` is the cone over the
rational normal curve, whose coordinate ring is the semigroup ring of

```text
S = {(0,0)} ∪ {(a,b) : a ≥ 1, 0 ≤ b ≤ d·a},   d = N − 1,
```

spanned by the monomials `U^a T^b` with `(a,b) ∈ S`.  `S` is saturated, so the ring is **normal**;
and `(m_0, m_{N−1}) = (U, U T^d)` is a **regular sequence of length 2 = dim**, because

```text
(a,b) + (0,d) ∈ S   ⟺   b ≤ d(a−1)   ⟺   (a,b) ∈ (1,0) + S      (for (a,b) ∈ S),
```

which is exactly the injectivity of multiplication by `U T^d` on the quotient by `(U)`.  With
`isCohenMacaulayRing_of_quotient` and `trdeg_hankelSecantQuotient` this gives CM for `C_{m−1}`.

For general `r` the ring is not a semigroup ring and the route is the classical one:

```text
in_degLex(I) is generated by the diagonal monomials of the consecutive-row minors — squarefree,
    hence a Stanley–Reisner ideal            (the Gröbner basis is corpus-owned:
                                              DeningerHankelHigherRankGroebner)
that complex is shellable                    ⟹  S/in(I) is Cohen–Macaulay
Gröbner degeneration                         ⟹  S/I is Cohen–Macaulay
```

The corpus already has a large Stanley–Reisner development (`StanleyReisner*`, 30+ modules) but no
shellability and no Gröbner degeneration; both must be built.  Normality then follows from Serre:
`R1` is the codimension-2 singular locus just proved, and `S2` is Cohen–Macaulayness.

### Monomial-algebra machinery for the `r = 1` stratum

```text
HTGeometry/MonomialSpan.lean
    monomialSpan, mem_monomialSpan_iff       membership is a support condition
    mul_mem_monomialSpan, one_mem_monomialSpan
        the monomial span of an additive submonoid of exponents is a subalgebra

HTGeometry/MonomialRegularity.lean
    support_mul_monomial_one                 (missing from mathlib)
    mem_monomial_mul_monomialSpan_iff        the principal monomial ideal is again a support
                                             condition — support inside the translated semigroup
    monomial_regular_of_semigroup
        ** a monomial is a nonzerodivisor modulo another exactly when, in the exponent semigroup,
           translation by the second reflects membership in the translate by the first **
```

That reduces the `r = 1` Cohen–Macaulay statement to the semigroup computation already recorded:
for `S = {(0,0)} ∪ {(a,b) : a ≥ 1, b ≤ d a}`, `α = (1,0)` and `β = (0,d)`,

```text
(a,b) ∈ S  and  (a, b+d) ∈ S   ⟹   b ≤ d(a−1)   ⟹   (a,b) ∈ (1,0) + S ,
```

which is exactly the hypothesis `hrefl` of `monomial_regular_of_semigroup`.

### The `r = 1` stratum is Cohen–Macaulay (Lean, 2026-08-30)

`HTGeometry/RationalNormalCone.lean` closes the last stratum `C_{m-1}` — the cone over the rational
normal curve of degree `d = 2m - 2` — unconditionally:

```text
coneExp d = {(a,b) : b ≤ d·a}            the exponent semigroup
rationalNormalCone K d                   its monomial subalgebra of K[U,T]
coneExp_refl_translate                   (a,b), (a,b+d) ∈ S ⟹ (a,b) ∈ (1,0) + S
isRegularOn_coneTop                      hence U T^d is a nonzerodivisor modulo U
isRingRegularSeq_cone                    ** (U, U T^d) is a ring-regular sequence **
isIntegral_cone                          (U T^i)^d = U^(d-i)·(U T^d)^i, so the cone ring is
                                         integral over K[U, U T^d]
ringKrullDim_le_of_isIntegral            ** Krull dimension does not grow along an integral
                                         extension ** (absent from mathlib)
ringKrullDim_rationalNormalCone          dim = 2
isCohenMacaulayRing_rationalNormalCone   ** the cone is Cohen–Macaulay **
```

The dimension is pinned from both sides: the regular sequence gives `2 ≤ dim` through
`length_le_ringKrullDim_of_isRingRegularSeq`, and integrality over the two-variable polynomial ring
gives `dim ≤ 2`.

**What is left for the general stratum.**  For `r ≥ 2` the secant ring is no longer a monomial
algebra, so the semigroup argument does not apply.  The two routes that do are (a) Conca's
specialisation — the generic Hankel matrix is the generic matrix cut by the anti-diagonal
identifications, which form a regular sequence on the generic determinantal ring, so
Hochster–Eagon transfers; and (b) the squarefree initial ideal → Stanley–Reisner → shellability
degeneration.  Both need machinery that neither mathlib nor this corpus has; (a) is the shorter of
the two because `isCohenMacaulayRing_of_quotient` already consumes exactly that shape.

Normality of the `r = 1` stratum is the next brick: `coneExp d` is saturated, and the missing Lean
input is the monomial valuation `min {d·e₀ − e₁ : e ∈ supp p}` together with its multiplicativity.

### … and normal (Lean, 2026-08-30)

`HTGeometry/MonomialValuation.lean` builds the missing valuation and
`HTGeometry/RationalNormalConeNormal.lean` applies it:

```text
minWeight w p                     min { weight w e : e ∈ supp p }
minWeight_mul                     ** additive — the lowest-weight forms multiply without
                                     cancellation ** (absent from mathlib)
minWeight_pow
weightNonneg K w                  the subalgebra cut out by weight ≥ 0
mem_weightNonneg_of_monic_relation
mem_weightNonneg_of_isIntegral    ** weight ≥ 0 is integrally closed in the polynomial ring **

rationalNormalCone_eq_weightNonneg          coneExp d is the non-negative part of (d, −1)
mem_rationalNormalCone_of_isIntegral        integrally closed inside K[U,T]
exists_mem_rationalNormalCone_of_relation_fractionRing
    ** normal: an element of the fraction field integral over the cone ring is already in it **
```

The additivity proof is at the coefficient level: if `weight e = minWeight p + minWeight q` then
every antidiagonal pair contributing to `coeff e (p q)` has both entries of minimal weight, so
`coeff e (p q) = coeff e (lowestForm p · lowestForm q)`, and that product is nonzero in a domain.
The normality argument is then the classical lowest-form one: `z ^ n` has weight `n μ` while every
other term of a monic relation has weight at least `(n−1) μ`, and `n μ ≥ (n−1) μ` fails for `μ < 0`.

The fraction-field statement uses that `K[U,T]` is a UFD, hence integrally closed, to place the
element in `K[U,T]` first.

**Stratum `C_{m−1}` is therefore closed: normal and Cohen–Macaulay, unconditionally.**  What remains
of the card's last clause is the same statement for `r ≥ 2` and rational singularities.

### Brick 1 of the general-`r` route is closed: the standard monomials (Lean, 2026-08-30)

`HTGeometry/HankelStandardMonomials.lean`.  The corpus already owned the degree-lex Gröbner basis
(`finiteHankelSecant_degLex_isGroebnerBasis`) and the standard-monomial predicate
(`FiniteHankelChainReduced`, with `hankelChainReduced_iff_colorable`).  What was missing is the
converse of `exists_finiteHankelMinor_diagonal_le_of_not_chainReduced` and the structural
consequence:

```text
not_finiteHankelChainReduced_of_diagonal_le
    the support of a canonical minor's leading diagonal is an (r+1)-chain, so an exponent above it
    is not chain-reduced
hankelStandardSpan K N r                     the span of the chain-reduced monomials
isCompl_finiteHankelSecantIdeal_standardSpan
    ** the chain-reduced monomials are a complement of the secant ideal **
finiteHankelChainIdeal K N r                 the initial monomial ideal
isCompl_finiteHankelChainIdeal_standardSpan
    ** and a complement of the initial monomial ideal **
hankelDegenerationLinearEquiv
    ** the secant quotient and its monomial degeneration are K-isomorphic **
```

Existence of the normal form is Gröbner division; uniqueness is the Gröbner-basis property
(`reduced_mem_span_eq_zero`).  One and the same set of monomials is a `K`-basis of both quotients —
the Hilbert-function equality of the degeneration in its sharpest, basis-level form.

**Remaining for general `r`.**

- *Brick 1a (graded refinement) — **CLOSED**.*  `HTGeometry/HankelGradedDegeneration.lean`:
  `isHomogeneous_finiteHankelMaximalMinorOver` (the minors are determinants of matrices of
  variables, hence homogeneous of degree `r+1`), `homogeneousComponent_mem_finiteHankelSecantIdeal`
  (**the secant ideal is homogeneous**), `homogeneousComponent_mem_hankelStandardSpan` (the
  standard span is graded), and `isHomogeneous_standardForm` (**the normal form of a homogeneous
  polynomial is homogeneous of the same degree**).  So `hankelDegenerationLinearEquiv` is
  degree-by-degree: the secant ring and its monomial degeneration have the same Hilbert function,
  witnessed by one common monomial basis.
- *Brick 2 (combinatorics of the complex) — **CLOSED**.*
  `HTGeometry/HankelChainFaces.lean` pins the face size of
  `Δ_r = {S : S contains no r+1 elements pairwise at distance ≥ 2}` from both sides:
  `card_support_le_two_mul_of_chainReduced` (the `r`-colouring of
  `hankelAdjacentDecompositionOfReduced` splits a face into `r` pieces, each on two consecutive
  indices, so `|S| ≤ 2r`), `card_le_of_pairwise_chainAdj` (halving is injective on a `2`-separated
  set), and `finiteHankelChainReduced_initialSegment` together with
  `card_support_initialSegmentExponent` (`{0,…,2r-1}` **is** a face, with `2r` vertices).  So
  `dim Δ_r = 2r - 1` and the degeneration has Krull dimension `2r` — the card's `(11)` on the
  monomial side.
- *Brick 2b, first step — **CLOSED**.*  `HTGeometry/CoordinatePrimeRegular.lean`:
  `isPrime_span_X_image` (**the coordinate ideal `(X i : i ∈ T)` is prime** — proved by reusing
  `minWeight_mul`: membership is positivity of the `{0,1}`-weight of `T`, which is additive on
  products) and `isRegularOn_of_notMem_inf_primes` (**an element outside every prime of a finite
  intersection is a nonzerodivisor modulo it** — three lines, no primary decomposition).  With
  `stanleyReisnerIdeal_eq_inf_facetIdeal` this says: a linear form whose support meets every facet
  is a nonzerodivisor on the Stanley–Reisner ring, i.e. the first step of a regular sequence on the
  degeneration.
- *Brick 2b, rest.*  Regularity of the **later** terms of the sequence — the quotients are no
  longer Stanley–Reisner rings, so this is the genuine Cohen–Macaulay content.  Route:
  shellability of `Δ_r`.
- *Brick 3.*  Transfer of a regular sequence of linear forms from the degeneration to the secant
  ring, using Brick 1a.
- *Brick 4, monomial side — **CLOSED**.*  `HTGeometry/KrullDimInfPrimes.lean`:
  `ringKrullDim_quotient_le_of_inf_primes` (a chain of primes above `⋂ P i` has its bottom above one
  of the `P i`, hence lies entirely above that one), `ringKrullDim_quotient_le_of_le`, and
  `ringKrullDim_quotient_inf_primes` — **the dimension of a quotient by a finite intersection of
  primes is the largest of the dimensions of the pieces**.  Neither statement is in mathlib.  With
  `stanleyReisnerIdeal_eq_inf_facetIdeal` and the face bound of `HankelChainFaces.lean` this
  computes the Krull dimension of the degeneration from its largest face, `2r`.  The per-prime input
  is `HTGeometry/CoordinateQuotient.lean`: `ker_killCompl` (**the kernel of `killCompl` is exactly
  the coordinate ideal of the complement of the range**), `quotientSpanXImageEquiv` (the quotient by
  a coordinate ideal is the polynomial ring on the surviving variables), and
  `ringKrullDim_quotient_span_X_image` (**its dimension is the number of surviving variables**).
- *Brick 4, secant side — **CLOSED**.*  `HTGeometry/KrullDimTrdeg.lean`:
  `ringKrullDim_le_of_trdeg_le` (**Krull dimension is at most the transcendence degree for a
  finitely generated algebra over a field** — mathlib's Noether normalization
  `exists_integral_inj_algHom_of_fg` embeds a polynomial ring on `s` variables integrally,
  `ringKrullDim_le_of_isIntegral` bounds the dimension by `s`, and `trdeg_le_of_injective` bounds
  `s` by the transcendence degree; the statement is not in mathlib), and hence
  `ringKrullDim_hankelSecantQuotient_le` — **the secant quotient has Krull dimension at most `2r`**.

  With `length_le_ringKrullDim_of_isRingRegularSeq` bounding the dimension below by the length of
  any ring-regular sequence, **a ring-regular sequence of length `2r` on the secant ring is now the
  single remaining input for `IsCohenMacaulayRing`** — the dimension equality comes for free.

### The degeneration is a Stanley–Reisner ring of dimension exactly `2r` (Lean, 2026-08-30)

`HTGeometry/HankelChainStanleyReisner.lean` closes the dimension count on the monomial side, end to
end and unconditionally:

```text
IsChainFace, IsChainFace.subset               the faces and their downward closure
finiteHankelChainReduced_iff_isChainFace      chain-reduced exponents are exactly the faces
finiteHankelChainIdeal_eq_inf
    ** the initial ideal is ⋂ over faces of the complementary coordinate ideal — i.e. it IS the
       Stanley–Reisner ideal of Δ_r **
card_le_two_mul_of_isChainFace                every face has at most 2r vertices
ringKrullDim_quotient_span_X_compl            each piece has dimension = the size of its face
ringKrullDim_quotient_finiteHankelChainIdeal
    ** ringKrullDim (K[a] ⧸ in(I_r)) = 2r **   (for 2r ≤ N)
```

A monomial fails to be chain-reduced exactly when its support is contained in no face; faces are
downward closed, which is what turns "not a face" into the intersection over all faces.  The
supporting general theorems, all new, are `isPrime_span_X_image`, `ringKrullDim_quotient_inf_primes`
and `ringKrullDim_quotient_span_X_image`.

That is `(11)` for the degeneration.  What is still open on this card is unchanged: the *regularity*
of the later terms of a linear system of parameters (shellability of `Δ_r`), the transfer of a
regular sequence across the degeneration, and the Krull dimension of the secant quotient itself.

### Cohen–Macaulay transport (Lean, 2026-08-31)

`HTGeometry/CohenMacaulayTransport.lean`: `isRegularOn_ringEquiv`,
`isRingRegularSeq_map_ringEquiv`, and `IsCohenMacaulayRing.of_ringEquiv` — **the Cohen–Macaulay
property transports along a ring isomorphism**.  A ring isomorphism carries a ring-regular sequence
to one (regularity is membership in the nonzerodivisors of a quotient, and the quotients correspond
under `Ideal.quotientEquiv`) and preserves the Krull dimension.

This is what lets a Cohen–Macaulay computation done on a convenient presentation — the monomial
subalgebra `rationalNormalCone`, say — be read back on the quotient presentation
`MvPolynomial (Fin N) K ⧸ finiteHankelSecantIdeal K N r` that the card's statement uses.

**Card 11's state.**  Everything except one input is now in place:

```text
ringKrullDim_hankelSecantQuotient_le    dim (K[a] ⧸ I_r) ≤ 2r
length_le_ringKrullDim_of_isRingRegularSeq   any regular sequence bounds it below
IsCohenMacaulayRing.of_ringEquiv        the property moves between presentations
```

so **a ring-regular sequence of length `2r` on the secant ring is the single remaining input**; the
dimension equality then holds automatically and `IsCohenMacaulayRing` follows.  For `r = 1` that
sequence is `(U, U T^d)` and is proved (`isRingRegularSeq_cone`); for `r ≥ 2` it is the shellability
content and remains open.

### The cone ring is the algebra generated by the moments (Lean, 2026-08-31)

`HTGeometry/RationalNormalConeGenerators.lean`:

```text
exists_greedy_parts                b ≤ d·a ⟹ b splits into a parts, each ≤ d
prod_monomial_one                  a product of monomials is the monomial of the sum
monomial_mem_adjoin_coneGenSet     every cone monomial is a product of the generators U T ^ i
rationalNormalCone_eq_adjoin
    ** rationalNormalCone K d = Algebra.adjoin K {U T ^ i : i ≤ d} **
```

That is the identification matching the coordinate ring of the affine cone over the rational normal
curve with the image of the `r = 1` moment parameterisation `a_i ↦ c x ^ i`.  With
`IsCohenMacaulayRing.of_ringEquiv` it is what carries `isCohenMacaulayRing_rationalNormalCone` and
`mem_rationalNormalCone_of_isIntegral` over to the presentation
`MvPolynomial (Fin N) K ⧸ finiteHankelSecantIdeal K N 1` in which the card states its clause.

### `C_{m−1}` is Cohen–Macaulay in the card's own presentation (Lean, 2026-08-31)

`HTGeometry/HankelRankOneCohenMacaulay.lean` closes the `r = 1` stratum in the exact form the card
states it — as a quotient of the coefficient polynomial ring by the Hankel minor ideal, not merely
as "the cone":

```text
rankOneMomentHom                a_i ↦ U T ^ i
ker_rankOneMomentHom            ker = finiteHankelSecantIdeal K N 1
range_rankOneMomentHom          range = rationalNormalCone K (N-1)
hankelRankOneQuotientEquiv
    ** MvPolynomial (Fin N) K ⧸ finiteHankelSecantIdeal K N 1 ≃+* rationalNormalCone K (N-1) **
isCohenMacaulayRing_hankelSecantQuotient_one
    ** IsCohenMacaulayRing (MvPolynomial (Fin N) K ⧸ finiteHankelSecantIdeal K N 1) **   (N ≥ 2)
```

The kernel is the corpus's `finiteHankelSecantIdeal_eq_parameterization_ker` after renaming the atom
coordinates; the range is `Algebra.adjoin K {U T ^ i : i < N}`, which `rationalNormalCone_eq_adjoin`
identifies with the cone; and `IsCohenMacaulayRing.of_ringEquiv` carries the property across.

**The card's clause "every `C_k` is normal, Cohen–Macaulay" is therefore proved for `k = m−1`,
unconditionally and in the card's own language.**  For `k < m−1` (that is `r ≥ 2`) the single
remaining input is a ring-regular sequence of length `2r`, i.e. Conca's shellability theorem; every
other ingredient — the Gröbner degeneration, its Hilbert-function equality, the Stanley–Reisner
identification, both dimension bounds, and the transport — is now in place.

### Normality as the standard class (Lean, 2026-08-31)

`HTGeometry/RationalNormalConeIntegrallyClosed.lean`:

```text
exists_pow_mul_mem_rationalNormalCone   every polynomial enters the cone after U ^ k
coneIsFractionRing                      ** the cone and K[U,T] share a fraction field **
isIntegrallyClosed_rationalNormalCone   ** the cone is integrally closed — i.e. NORMAL **
```

Multiplying by `U ^ k` with `k` the `T`-degree pushes any polynomial into the cone, which gives the
fraction-field identification; the explicit normality theorem then upgrades to the standard
`IsIntegrallyClosed` class.

**Both halves of the card's clause for `k = m−1` are now standard-class statements:**
`isIntegrallyClosed_rationalNormalCone` (normal) and `isCohenMacaulayRing_hankelSecantQuotient_one`
(Cohen–Macaulay, in the card's own presentation).

### General Stanley–Reisner substrate (Lean, 2026-08-31)

`HTGeometry/StanleyReisnerDimension.lean` records the Hankel-specific arguments in the generality
they actually hold, for any finite family of faces:

```text
faceFamilyIdeal K F              ⋂ over the faces of the complementary coordinate ideal
ringKrullDim_faceFamilyIdeal     ** the dimension is the size of the largest face **
isRegularOn_faceFamilyIdeal      ** a form outside every facet prime is a nonzerodivisor **
```

These are the substrate a shellability argument builds on.  The remaining Cohen–Macaulay content for
`r ≥ 2` is exactly the regularity of the *later* terms of a linear system of parameters, where the
successive quotients stop being Stanley–Reisner rings.

`HTGeometry/StanleyReisnerBasis.lean` completes the general substrate:

```text
IsFaceFamily                                downward closure of a face family
mem_faceFamilyIdeal_iff                     membership is a support condition
isCompl_faceFamilyIdeal_faceMonomialSpan
    ** the monomials supported on faces are a K-basis of the Stanley–Reisner ring **
```

the general form of `isCompl_finiteHankelChainIdeal_standardSpan`, and the basis on which
Hilbert-series and shelling arguments are carried out.

`HTGeometry/StanleyReisnerDeletion.lean` adds the first of the two induction operations:

```text
faceDeletion F v               the faces avoiding v
isFaceFamily_faceDeletion      the deletion is again downward closed
faceFamilyIdeal_faceDeletion   ** I_{del(v)} = I_F + (X v) **
```

Split a polynomial by whether `v` occurs: the `v`-free part lies in `I_F`, the rest is divisible by
`X v`.  Deletion and link are what every induction on a simplicial complex uses — vertex
decomposability, shellability, and Reisner's criterion all reduce to those two operations — so this
is the first stone of the shellability development that `r ≥ 2` needs.

`HTGeometry/StanleyReisnerLink.lean` adds the second:

```text
faceLink F v                   the faces S with v ∉ S and S ∪ {v} a face
isFaceFamily_faceLink          the link is again downward closed
support_X_mul, support_single_add    multiplying by a variable translates the support
faceFamilyIdeal_faceLink       ** I_{lk(v)} = (I_F : X v) + (X v) **
```

With the deletion theorem this is the pair of reductions that vertex decomposability, shellability,
and Reisner's criterion all run on — the whole apparatus for an induction over the complex is now
available in Lean.

`HTGeometry/StanleyReisnerFacets.lean` makes the nonzerodivisor criterion usable:

```text
faceFacets F                     the maximal faces
exists_facet_superset            every face is contained in a facet
faceFamilyIdeal_eq_facets        ** the ideal only sees the facets **
IsConePoint F v, mem_of_isConePoint
isRegularOn_X_of_isConePoint
    ** the variable at a cone point is a nonzerodivisor on the Stanley–Reisner ring **
```

Over *all* faces the empty face is present and every variable lies in its coordinate prime, so
nothing is ever regular; restricting to facets is what makes `isRegularOn_faceFamilyIdeal` bite.
The cone-point case is the base case of the Cohen–Macaulay induction, `K[Δ]` being a polynomial
extension of `K[del(v)]` there.

### The first Cohen–Macaulay induction step for complexes (Lean, 2026-08-31)

`HTGeometry/StanleyReisnerCone.lean`:

```text
isRegularOn_bot_of_mem_nonZeroDivisors   a nonzerodivisor is regular modulo ⊥
quotXEquivDeletion                       (K[Δ] ⧸ X v) ≃+* K[del(v)]
card_le_of_mem_faceDeletion              the deletion loses exactly one from the face size
faceFamilyIdeal_faceDeletion_ne_top      the deletion ideal is proper
isCohenMacaulayRing_of_isConePoint
    ** at a cone point, K[del(v)] Cohen–Macaulay ⟹ K[Δ] Cohen–Macaulay **
```

`X v` is a nonzerodivisor (`isRegularOn_X_of_isConePoint`), cutting by it gives exactly the deletion
(`faceFamilyIdeal_faceDeletion`), and the dimension drops by one
(`ringKrullDim_faceFamilyIdeal`); `isCohenMacaulayRing_of_quotient` and
`IsCohenMacaulayRing.of_ringEquiv` assemble these into the transfer.

This is the first genuine Cohen–Macaulay induction step for simplicial complexes and the base case
of any vertex-decomposability or shellability argument.  The remaining content for `r ≥ 2` is the
inductive step at a *non-cone* vertex, where one needs `K[lk(v)]` and `K[del(v)]` together — the
link theorem `faceFamilyIdeal_faceLink` supplies the algebraic half of that.

### The degenerate range, and the shedding vertex for the induction (Lean, 2026-08-31)

`HTGeometry/HankelDegenerateRange.lean`:

```text
finiteHankelMaximalMinorSetOver_eq_empty       no canonical minors when N ≤ 2r
finiteHankelSecantIdeal_eq_bot                 so the ideal is ⊥
isCohenMacaulayRing_hankelSecantQuotient_of_le
    ** for N ≤ 2r the quotient is a polynomial ring, hence Cohen–Macaulay, for every r **
```

A canonical `(r+1)`-minor needs `2r + 1` coordinates — its column offsets are strictly increasing so
the last is at least `r`, and `r + 1 + c j ≤ N` forces `N ≥ 2r + 1`.

**The induction this is the base case of.**  In the chain complex `Δ_r` on `{0,…,N-1}`,
`del(0) = Δ_r` on `{1,…,N-1}` — the same complex with one fewer vertex — and `0` is a *shedding*
vertex: a facet of `del(0)` has `2r` elements, and adjoining `0` either raises the `2`-separated
count (when `1 ∉ S`) or the cardinality past `2r` (when `1 ∈ S`), so it stays a facet of `Δ_r`.  The
recursion on `N` therefore bottoms out exactly at `N ≤ 2r`, which is now closed.

**What is still missing is one general theorem:** the inductive step at a non-cone shedding vertex —
`K[del(v)]` and `K[lk(v)]` Cohen–Macaulay (of dimensions `d` and `d-1`) implies `K[Δ]` Cohen–Macaulay.
Its standard proof runs the depth lemma on
`0 → K[Δ] → K[del(v)] ⊕ K[st(v)] → K[lk(v)] → 0`, which needs depth for short exact sequences of
modules — the one piece of commutative algebra this development does not yet have.  The cone case
(`isCohenMacaulayRing_of_isConePoint`) is the degenerate instance of it that is already proved.

### Mathlib already has the depth tool — route correction (2026-08-31)

Searching mathlib (not just this corpus) for regular-sequence machinery turns up:

```text
Mathlib/RingTheory/Regular/RegularSequence.lean
    Ideal.ofList, RingTheory.Sequence.IsWeaklyRegular, RingTheory.Sequence.IsRegular
    — the module-theoretic regular sequence; for `M = R` this is exactly the
      `IsRingRegularSeq` of `CohenMacaulayDepth.lean`
Mathlib/RingTheory/Depth/Rees.lean
    ** exists_isRegular_tfae — the Rees theorem **: for a Noetherian ring, an ideal `I` and a
    finitely generated `M` with `I·M < M`, the existence of an `M`-regular sequence of length `n`
    inside `I` is equivalent to the vanishing of `Ext^i(R/I, M)` for `i < n`
```

That is precisely the tool the missing inductive step needs.  With Rees, "depth ≥ n" becomes an
Ext-vanishing statement, and the depth lemma for
`0 → K[Δ] → K[del(v)] ⊕ K[st(v)] → K[lk(v)] → 0`
follows from the long exact sequence of `Ext`, which mathlib also has.  So the non-cone inductive
step is **not** a from-scratch development after all; the plan is

1. bridge `IsRingRegularSeq` to `RingTheory.Sequence.IsRegular` (they agree for `M = R`);
2. define depth by Ext-vanishing and transport through Rees;
3. prove the depth lemma from the long exact `Ext` sequence;
4. apply it to the Mayer–Vietoris sequence of the complex at a shedding vertex.

The `Δ_r` side of the induction is already settled: `del(0)` is the same complex on one fewer
vertex, `0` is a shedding vertex, and the base case `N ≤ 2r` is
`isCohenMacaulayRing_hankelSecantQuotient_of_le`.

Step 1 of that plan is done: `HTGeometry/RegularSequenceBridge.lean`

```text
smul_quotient_eq_mk_mul          r • z = mk r * z on a quotient
isSMulRegular_quotient_iff       IsSMulRegular (R ⧸ I) x ↔ IsRegularOn I x
ofList_smul_top                  I • ⊤ = I inside R
isRingRegularSeq_iff_isRegular   ** IsRingRegularSeq rs ↔ RingTheory.Sequence.IsRegular R rs **
```

so every regular sequence in this development is a mathlib regular sequence, and the Rees theorem
applies to it directly.

### The Mayer–Vietoris pair (Lean, 2026-08-31)

`HTGeometry/StanleyReisnerMayerVietoris.lean` supplies the ideal-level input of the short exact
sequence the depth argument runs on:

```text
faceStar F v, isFaceFamily_faceStar, isConePoint_faceStar   the star, a cone with apex v
faceDeletion_union_faceStar        del(v) ∪ st(v) = Δ
faceDeletion_inter_faceStar        del(v) ∩ st(v) = lk(v)
faceFamilyIdeal_union              I_{F ∪ G} = I_F ⊓ I_G
faceFamilyIdeal_inter              I_{F ∩ G} = I_F ⊔ I_G
faceFamilyIdeal_deletion_inf_star  ** I_Δ = I_{del(v)} ⊓ I_{st(v)} **
faceFamilyIdeal_link_eq_sup        ** I_{lk(v)} = I_{del(v)} ⊔ I_{st(v)} **
```

The sum identity carries the content: split a polynomial by whether each monomial's support is a
face of `F`; the part that is not goes into `I_F`, and the part that is cannot also be a face of `G`,
so it goes into `I_G`.

Since `I_Δ = I_del ⊓ I_st` and `I_lk = I_del ⊔ I_st`, the standard exact sequence

```text
0 → K[x]/(I_del ⊓ I_st) → K[x]/I_del ⊕ K[x]/I_st → K[x]/(I_del ⊔ I_st) → 0
```

is exactly `0 → K[Δ] → K[del(v)] ⊕ K[st(v)] → K[lk(v)] → 0`.  The star is a cone
(`isConePoint_faceStar`), so `K[st(v)]` is Cohen–Macaulay whenever `K[lk(v)]` is, by
`isCohenMacaulayRing_of_isConePoint`.  What remains is the depth lemma along that sequence, for
which `isRingRegularSeq_iff_isRegular` now connects to mathlib's Rees theorem.

### The Mayer–Vietoris sequence itself (Lean, 2026-08-31)

`HTGeometry/MayerVietorisQuotient.lean` builds the short exact sequence for any two ideals:

```text
0 → R ⧸ (I ⊓ J) → (R ⧸ I) × (R ⧸ J) → R ⧸ (I ⊔ J) → 0

mvPair, mvDiff        the diagonal and the difference
mvPair_injective      exactness on the left
mvDiff_surjective     exactness on the right
mv_exact              ** range (mvPair) = ker (mvDiff) **
```

Exactness in the middle is the only step with content: if `α - β ∈ I ⊔ J`, write `α - β = i + j`
with `i ∈ I` and `j ∈ J`; then `α - i = β + j` is a common lift.

Instantiated at `I = I_{del(v)}`, `J = I_{st(v)}` — where
`faceFamilyIdeal_deletion_inf_star` and `faceFamilyIdeal_link_eq_sup` identify `I ⊓ J = I_Δ` and
`I ⊔ J = I_{lk(v)}` — this is exactly

```text
0 → K[Δ] → K[del(v)] ⊕ K[st(v)] → K[lk(v)] → 0 .
```

Everything the depth argument consumes is now present except the depth lemma itself: the sequence,
the identification of its three terms, `K[st(v)]` Cohen–Macaulay from `K[lk(v)]` by the cone
reduction, and — through `isRingRegularSeq_iff_isRegular` — mathlib's Rees theorem to convert
"regular sequence of length n" into Ext-vanishing.

### The depth lemma is available in mathlib — the route is now fully mapped (2026-08-31)

`Mathlib/Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean` has the long exact `Ext`
sequence in any abelian category:

```text
covariantSequence_exact :
  Ext X S.X₁ n₀ → Ext X S.X₂ n₀ → Ext X S.X₃ n₀ → Ext X S.X₁ n₁ → Ext X S.X₂ n₁ → Ext X S.X₃ n₁
  exact, for a short exact S and n₀ + 1 = n₁
```

Its tail `Ext^{n₀}(k, C) → Ext^{n₁}(k, A) → Ext^{n₁}(k, B)` is precisely the depth lemma: if
`Ext^{n₀}(k, C) = 0` and `Ext^{n₁}(k, B) = 0` then exactness forces `Ext^{n₁}(k, A) = 0`.  So

```text
depth A ≥ min (depth B, depth C + 1)
```

which with `A = K[Δ]`, `B = K[del(v)] ⊕ K[st(v)]` (depth `d`) and `C = K[lk(v)]` (depth `d-1`)
gives `depth K[Δ] ≥ d` — the missing inductive step.

**Every ingredient is now identified and in place.**  The remaining execution, in order:

1. express the Mayer–Vietoris sequence of `MayerVietorisQuotient.lean` as a `ShortComplex` in
   `ModuleCat (MvPolynomial σ K)` and prove it `ShortExact` (the three lemmas
   `mvPair_injective`, `mv_exact`, `mvDiff_surjective` are exactly its content);
2. define depth by `Ext`-vanishing and transport it to regular sequences with mathlib's Rees
   theorem `exists_isRegular_tfae`, using `isRingRegularSeq_iff_isRegular` as the bridge;
3. apply `covariantSequence_exact` to get `depth A ≥ min (depth B, depth C + 1)`;
4. run the induction at the shedding vertex `0` of `Δ_r`, whose base case `N ≤ 2r` is
   `isCohenMacaulayRing_hankelSecantQuotient_of_le` and whose cone case is
   `isCohenMacaulayRing_of_isConePoint`;
5. transfer from the degeneration to the secant ring using the graded standard-monomial
   equivalence (`hankelDegenerationLinearEquiv`, `isHomogeneous_standardForm`).

No step now depends on a theorem that is absent from mathlib or from this corpus.

**Step 1 of that route is done.**  `HTGeometry/MayerVietorisShortExact.lean`:

```text
mvDiff_comp_mvPair         the composite vanishes
mvShortComplex I J         0 → R ⧸ (I ⊓ J) → (R ⧸ I) × (R ⧸ J) → R ⧸ (I ⊔ J) → 0
mvShortComplex_shortExact  ** it is a ShortExact ShortComplex in ModuleCat R **
```

`ModuleCat.mono_iff_injective`, `ModuleCat.epi_iff_surjective` and
`ShortComplex.moduleCat_exact_iff` turn the three conditions into the injectivity, exactness and
surjectivity already proved.  So `covariantSequence_exact` can now be applied to this complex, which
is the whole of step 3.

**Step 3 is done too.**  `HTGeometry/DepthLemma.lean`:

```text
subsingleton_ext_of_shortExact
    ** Ext^{n₀}(X,C) = 0 and Ext^{n₁}(X,B) = 0  ⟹  Ext^{n₁}(X,A) = 0,  n₀+1 = n₁ **
subsingleton_ext_mv
    its instance along the Mayer–Vietoris sequence of two ideals
```

i.e. `depth A ≥ min (depth B, depth C + 1)` once depth is read from `Ext`-vanishing.  The proof is
`Ext.covariant_sequence_exact₁`: a class in `Ext^{n₁}(X,A)` that dies in `Ext^{n₁}(X,B)` comes from
`Ext^{n₀}(X,C)`, and that group is zero.

With `I = I_{del(v)}`, `J = I_{st(v)}` this is exactly the inductive step at a non-cone vertex.  The
only remaining link in the chain is **step 2**: the translation between `Ext`-vanishing and the
existence of a regular sequence, for which mathlib's Rees theorem `exists_isRegular_tfae` and the
bridge `isRingRegularSeq_iff_isRegular` are both in place.

**Step 2 is done.**  `HTGeometry/ReesDepth.lean`:

```text
exists_isRegular_of_ext, ext_subsingleton_of_isRegular   both directions of Rees, for modules
smul_top_lt_top_of_ne_top                                the hypothesis, for M = R
exists_isRingRegularSeq_of_ext
    ** Ext-vanishing ⟹ a ring-regular sequence of length n inside I **
ext_subsingleton_of_isRingRegularSeq                     ** and back **
```

So the chain

```text
regular sequences on K[del(v)] and K[lk(v)]
  → Ext-vanishing                        ReesDepth
  → Ext-vanishing for K[Δ]               DepthLemma, along MayerVietorisShortExact
  → a regular sequence on K[Δ]           ReesDepth, back again
```

is now complete as a chain of proved theorems.  Steps 1, 2 and 3 of the route are closed; what is
left is the bookkeeping of steps 4 and 5 — running the induction at the shedding vertex `0` of
`Δ_r` (base case and cone case already proved, Mayer–Vietoris pair already proved) and transferring
the conclusion from the degeneration to the secant ring (`hankelDegenerationLinearEquiv` and
`isHomogeneous_standardForm` already proved).

`HTGeometry/DepthTransfer.lean` assembles the depth lemma over a whole range, handling the one extra
case (`i = 0`, where the long exact sequence has no preceding term) by the hom functor and the
monomorphism:

```text
subsingleton_ext_zero_of_mono      degree-zero vanishing passes to a subobject
subsingleton_ext_lt_of_shortExact
    ** Ext^i(X,B) = 0 for i < n₁ and Ext^i(X,C) = 0 for i < n₀  ⟹  Ext^i(X,A) = 0 for i < n₁ **
```

Read through `ReesDepth.lean` this is `depth A ≥ min (depth B, depth C + 1)` in exactly the form the
Cohen–Macaulay induction consumes.

`HTGeometry/ExtMiddleProduct.lean` supplies the last general ingredient of the induction, the middle
term of the Mayer–Vietoris sequence being a direct sum:

```text
subsingleton_ext_middle_of_shortExact       both outer terms vanish ⟹ the middle vanishes
subsingleton_ext_middle_lt_of_shortExact    the same over a range
prodShortComplex, prodShortComplex_shortExact   0 → A → A × B → B → 0
subsingleton_ext_prod                       ** Ext-vanishing passes to a binary product **
```

so `K[del(v)] ⊕ K[st(v)]` is deep as soon as both summands are, and — `st(v)` being a cone over
`lk(v)` — both are Cohen–Macaulay of dimension `d` by the inductive hypothesis plus
`isCohenMacaulayRing_of_isConePoint`.

**Every general theorem the induction needs is now proved.**  What is left on this card is purely
the assembly: instantiate the chain at `Δ_r` with the shedding vertex `0`, run the recursion on `N`
down to the base case `N ≤ 2r`, and carry the conclusion to the secant ring along the graded
standard-monomial equivalence.

### The shedding step is proved (Lean, 2026-08-31)

`HTGeometry/SheddingStep.lean` assembles the whole apparatus into the induction step itself:

```text
subsingleton_ext_mv_lt
    ** R ⧸ I and R ⧸ J deep to n₁, R ⧸ (I ⊔ J) deep to n₀  ⟹  R ⧸ (I ⊓ J) deep to n₁ **
subsingleton_ext_faceFamily
    ** deletion and star deep to n₁, link deep to n₀  ⟹  the complex deep to n₁ **
```

the second being the first at `I = I_{del(v)}`, `J = I_{st(v)}`, where
`faceFamilyIdeal_deletion_inf_star` and `faceFamilyIdeal_link_eq_sup` identify `I ⊓ J = I_Δ` and
`I ⊔ J = I_{lk(v)}`.  Since the star is a cone over the link, its ring is deep whenever the link's
is, so in practice the hypotheses read "the deletion and the link are Cohen–Macaulay of dimensions
`d` and `d-1`" and the conclusion is depth `d` for the complex.

**This was the theorem the card was blocked on.**  It is proved, in general, for every face family
and every vertex.  What remains is the instantiation at `Δ_r`: the recursion on `N` with shedding
vertex `0`, bottoming out at `N ≤ 2r`, and the transfer to the secant ring.

`HTGeometry/SheddingRegularSequence.lean` puts the whole chain back into regular-sequence language:

```text
exists_isRegular_mv
    ** regular sequences of length n₁ on R ⧸ I and R ⧸ J inside 𝔪, one of length n₀ on
       R ⧸ (I ⊔ J)  ⟹  one of length n₁ on R ⧸ (I ⊓ J) **
exists_isRegular_faceFamily
    ** deletion and star of length n₁, link of length n₀  ⟹  the complex of length n₁ **
```

Rees forwards, the shedding step across the Mayer–Vietoris sequence, Rees backwards.  Everything the
Cohen–Macaulay definition speaks about is now available as a proved theorem; the remaining work on
this card is the recursion at `Δ_r` with shedding vertex `0` and the transfer to the secant ring.

### Both steps of the recursion are now regular-sequence theorems (Lean, 2026-08-31)

`HTGeometry/ConeRegularSequence.lean` supplies the cone case:

```text
faceFamilyIdeal_le_deletion    I_F ≤ I_{del(v)}
quotSMulTopEquivDeletion       ** QuotSMulTop (X v) K[Δ] ≃ₗ K[del(v)] **
exists_isRegular_cone
    ** a regular sequence of length n on K[del(v)] gives one of length n+1 on K[Δ] **
```

The module isomorphism carries the content: the kernel of `K[Δ] → K[del(v)]` is exactly
`X v · K[Δ]`, because `I_{del(v)} = I_F + (X v)`.  `RingTheory.Sequence.isRegular_cons_iff` and
`LinearEquiv.isRegular_congr` then give the sequence statement.

So the two steps of the Cohen–Macaulay recursion over a simplicial complex —

```text
exists_isRegular_cone          at a cone point
exists_isRegular_faceFamily    at a shedding vertex
```

— are both proved, in the vocabulary the Cohen–Macaulay definition uses.  The only work left on this
card is the combinatorial instantiation at `Δ_r`: identify `del(0)` and `lk(0)` of the chain complex,
run the recursion on `N` to the base case `N ≤ 2r`, and transfer to the secant ring.

### Correction: the instantiation needs a larger class of complexes than `Δ_r`

Computing the link of the first vertex shows the recursion does **not** close on the family
`{Δ_r}`.  Writing `γ(S)` for the largest number of elements of `S` that are pairwise at distance at
least two, so that `Δ_r = {S : γ(S) ≤ r}`:

```text
γ(S ∪ {0}) = γ(S)      when 1 ∈ S      (the greedy scan picks 0 in place of 1)
γ(S ∪ {0}) = γ(S) + 1  when 1 ∉ S
```

so `lk_{Δ_r}(0) = {S ⊆ [1,N) : γ(S ∪ {0}) ≤ r}`, which is neither `Δ_r` nor `Δ_{r-1}` — it is
"`Δ_r` with the vertex `0` forced into every face".  The class that *is* closed under both
operations is

```text
Δ_r^A = { S : γ(S ∪ A) ≤ r }      for a fixed set A of forced vertices,

  Δ_r^∅            = Δ_r
  del_{Δ_r^A}(v)   = Δ_r^A   on the vertices ≠ v
  lk_{Δ_r^A}(v)    = Δ_r^{A ∪ {v}}  on the vertices ≠ v
```

and the recursion should run on `(A, remaining vertex set)`, with the dimension being
`min(#vertices, 2r − γ(A))` and the base case the full simplex.  This is more than the relabelling
bookkeeping the previous entry assumed; identifying this closed class is the substance of the
combinatorial half of Conca's argument, and it is now written down.

Both algebraic steps of the recursion (`exists_isRegular_cone`, `exists_isRegular_faceFamily`) are
proved and independent of this; what is outstanding is exactly:

1. define `Δ_r^A` and prove `IsFaceFamily`, the deletion and link identities above;
2. compute its facets and dimension (`γ(S) ≥ ⌈|S|/2⌉` and the initial-segment face give both bounds,
   as in `HankelChainFaces.lean`);
3. run the recursion, bottoming out at the simplex;
4. transfer to the secant ring by `hankelDegenerationLinearEquiv` and `isHomogeneous_standardForm`.

**Item 1 of that list is done.**  `HTGeometry/ChainForcedFamily.lean`:

```text
chainForcedFamily N r A            the complex Δ_r^A = {S : S ∪ A has no (r+1)-chain}
chainForcedFamily_empty            Δ_r^∅ = Δ_r
isFaceFamily_chainForcedFamily     it is downward closed
faceLink_chainForcedFamily
    ** lk (Δ_r^A) v = del (Δ_r^{A ∪ {v}}) v — the class IS closed under links **
card_add_card_le_of_mem_chainForcedFamily
    a face disjoint from the forced set has at most 2r − |A| vertices
```

Deletion needs no lemma — `del (Δ_r^A) v` is `Δ_r^A` restricted to faces avoiding `v`, by
definition.  The link identity is the substantive one, and it is what lets the two recursion steps
run on the pair `(A, remaining vertices)`.

Outstanding: the facet/dimension computation for `Δ_r^A`, the recursion itself, and the transfer to
the secant ring.

### The star hypothesis is redundant (Lean, 2026-08-31)

`HTGeometry/StarReduction.lean`:

```text
faceDeletion_faceStar        del (st(v)) v = lk(v)
exists_isRegular_star        a sequence of length n on the link gives one of length n+1 on the star
exists_isRegular_shedding
    ** the recursion step needs only the deletion (length n₀+1) and the link (length n₀) **
```

The star is a cone with apex `v` and deleting the apex returns the link, so the star's depth follows
from the link's by `exists_isRegular_cone`.  That collapses the shedding step from three hypotheses
to two, and is the form the recursion over a complex actually runs in: at each vertex one descends
to the deletion and the link, and the star takes care of itself.

**Outstanding on this card, precisely.**  Write `d(A, V) = max { |S| : S ⊆ V, γ(S ∪ A) ≤ r }` for
the dimension of `Δ_r^A` on an available vertex set `V`.  What is needed is the shedding property of
the smallest available vertex `v`:

```text
d(A, V \ {v})      = d(A, V)        the deletion keeps the dimension
d(A ∪ {v}, V \ {v}) = d(A, V) - 1   the link drops it by one
```

together with the base case (`V` small enough that `Δ_r^A` is the full simplex on `V`) and the
transfer to the secant ring.  Every algebraic input is proved; this is the whole of what remains.

`HTGeometry/ChainForcedOn.lean` makes the available vertex set explicit, so the recursion descends
on the pair `(A, V)`:

```text
Δ_r^{A,V} = { S ⊆ V : S ∪ A contains no (r+1)-chain }

chainForcedOn_univ           Δ_r^{A,univ} = Δ_r^A
isFaceFamily_chainForcedOn   downward closed
faceDeletion_chainForcedOn   ** del v = Δ_r^{A, V \ {v}} **
faceLink_chainForcedOn       ** lk v  = Δ_r^{A ∪ {v}, V \ {v}} **   (for v ∈ V)
```

Both operations shrink `V` by one vertex, so the two-hypothesis recursion of `StarReduction.lean` is
well founded on `V.card`.  Everything structural is now in place; what is left is exactly the
dimension bookkeeping stated above.

### What the dimension bookkeeping actually requires — analysis (2026-08-31)

In the recursion the forced set sits to the left of the available set: shedding always takes
`v = min V`, so `A ⊆ [0, v)` and `V ⊆ [v, N)`.  Write `d(A,V) = max { |S| : S ⊆ V, γ(S ∪ A) ≤ r }`.

The link identity `d(A ∪ {v}, V∖{v}) = d(A,V) − 1` is equivalent to

```text
some maximum-size face of Δ_r^{A,V} contains v = min V .
```

**The naive exchange argument fails.**  One would like to take a maximum face `S` with `v ∉ S` and
replace `min S` by `v`.  That is not safe: moving an element left can *increase* the number of
pairwise `2`-separated elements — for `r = 1`, `S = {5,6}` has `γ = 1` but `{2,6}` has `γ = 2`.  So
the swap must be argued differently.

**The construction that should work** is greedy from the left: scan `V` in increasing order and keep
each vertex whose addition preserves `γ(· ∪ A) ≤ r`.  The resulting face contains `v` whenever `{v}`
is a face, and for these chain complexes it should be of maximum size — but that is an exchange
property, and the complex is *not* a matroid (for `r = 1`, `F = {0,1}` and `G = {5,6}` are facets
with no valid exchange), so the maximality needs its own proof rather than a matroid citation.

The deletion identity `d(A, V∖{v}) = d(A,V)` is the shedding condition proper, and follows from the
same greedy construction applied to `V∖{v}`.

This is the entire remaining mathematical content of the card; everything algebraic —
`exists_isRegular_shedding`, `exists_isRegular_cone`, `faceDeletion_chainForcedOn`,
`faceLink_chainForcedOn`, `ringKrullDim_faceFamilyIdeal`, the base case and the transfer inputs — is
proved.

### The recursion collapses to two shapes — the last step is now a bounded induction

Two observations reduce the whole remaining problem.

**1. Only two numbers of the forced set matter.**  Because shedding always takes `v = min V`, the
available set stays a final interval `V = [k, N)` and the forced set stays inside `[0, k)`.  The
greedy left-to-right scan computing `γ` traverses `A` before `S`, so

```text
γ(S ∪ A) = γ(A) + g_m(S) ,
```

where `m` is the last element the greedy takes inside `A` and `g_m` is the greedy count on `S`
starting from "last taken `= m`".  So the face condition is `g_m(S) ≤ r'` with `r' = r − γ(A)`, and
the complex depends on `A` only through the pair `(m, r')`.

**2. There are then exactly two shapes.**  Since `m < k`:

```text
k ≥ m + 2 :  every element of S is ≥ m+2, so g_m = γ, and the complex is
             Δ_{r'} on the interval [k, N)                              (shape I)

k = m + 1 :  the greedy skips k and restarts at k+1, so the complex is the
             cone with apex k over Δ_{r'} on [k+1, N)                   (shape II)
```

Shape II needs no shedding at all — `k` is a cone point, so `exists_isRegular_cone` applies.

**3. The recursion.**  For shape I on `[k, N)` with parameter `r'`, shedding at `k` gives

```text
deletion :  shape I on [k+1, N) with r'          (same parameter, shorter interval)
link     :  shape II with r' − 1, i.e. a cone over shape I on [k+2, N) with r' − 1
```

so a double induction on `(N − k, r')`, bottoming out at `r' = 0` (only the empty face) and at short
intervals (the full simplex, `isCohenMacaulayRing_hankelSecantQuotient_of_le`).

**4. The dimension is now immediate.**  For shape I the maximum face is the *initial* sub-interval
`[k, k + min(N−k, 2r'))` — an interval of length `L` has `γ = ⌈L/2⌉`, so it is a face exactly when
`L ≤ 2r'`.  Being initial it contains `k`, which is precisely the shedding condition that the naive
exchange argument failed to give.

So the remaining work is: define the two shapes, prove the greedy decomposition `γ(S ∪ A) =
γ(A) + g_m(S)`, identify deletion and link as above, and run the double induction.  No step needs a
theorem that is not already proved.

**Point 4 of the reduction is proved.**  `HTGeometry/ChainInterval.lean`:

```text
card_le_of_pairwise_chainAdj_interval   a 2-separated subset of an interval of length 2M has at
                                        most M elements (halving after shifting to the origin)
intervalFinset N a L                    the interval [a, a+L) of variables
isChainFace_intervalFinset              ** an interval of length ≤ 2r is a face of Δ_r **
card_intervalFinset                     it has L vertices
mem_chainForcedOn_intervalFinset        and it is a face of the complex on itself
```

Combined with `card_le_two_mul_of_isChainFace` (every face has at most `2r` vertices), the interval
of length `2r` starting at *any* vertex is a maximum face.  Starting it at the least available
vertex gives the shedding condition — the thing the naive exchange argument could not deliver.

### Everything now reduces to one classical lemma: `γ` is computed by the greedy scan

Tracing the two shapes to their roots, every remaining step is an instance of the same fact.

*Why shape II is a cone.*  After shedding at `k`, the forced set is `A' = A ∪ {k}` whose greedy scan
ends at `k`, and the available set is `[k+1, N)`.  The apex claim is that adjoining `k+1` to a face
never increases `γ(· ∪ A')` — which holds because the greedy, having last taken `k`, *skips* `k+1`
(it is not `2`-separated from `k`).  That is exactly "the greedy count is the maximum".

*Why the naive exchange fails without it.*  Replacing `k+1` by `k` inside a chain is unsound: an
element `k−1` of `A` is `2`-separated from `k+1` but not from `k`.  The greedy avoids the issue by
never selecting `k+1` in the first place.

So the one general lemma still to prove is the classical activity-selection statement

```text
γ(T) = the number of elements taken by the left-to-right greedy scan of T
       (take an element iff it exceeds the previous taken one by at least 2)
```

together with its immediate corollary, additivity across a left/right split:

```text
γ(S ∪ A) = γ(A) + g_m(S)   for A entirely to the left of S, m = last greedy element of A .
```

Given those, the two shapes, the deletion and link identities, and the dimension all follow from
material already proved (`ChainInterval.lean`, `ChainForcedOn.lean`, `StarReduction.lean`), and the
double induction on `(N−k, r')` closes the card.

### The greedy lemma is proved (Lean, 2026-08-31)

`HTGeometry/ChainGreedy.lean`:

```text
chainGreedy T                    the greedy left-to-right selection
chainGreedy_pairwise             ** it is 2-separated **
card_le_card_chainGreedy         ** it is optimal: every 2-separated subset is no larger **
isChainFace_iff_card_chainGreedy
    ** S is a face of Δ_r exactly when its greedy selection has at most r elements **
```

Optimality is the classical activity-selection argument in its cleanest recursive form: a
`2`-separated subset has at most one element in `{m, m+1}` for `m` the least element of the ambient
set, and the rest is a `2`-separated subset of what survives the filter, so it is at most `1 +` the
greedy count of that — which is the greedy count of the whole.

**This was the one general lemma the previous entry named as outstanding.**  With it, `γ` is
computable, the additivity across a left/right split follows, the star of a shed vertex is a cone
(the greedy, having just taken `k`, skips `k+1`), and the two shapes of the recursion are
identified.  What is left on this card is assembling those identifications and running the double
induction on `(N − k, r')`.

### The cone property is proved (Lean, 2026-08-31)

`HTGeometry/ChainGreedySucc.lean`:

```text
chainGreedy_insert_succ   ** x ∈ chainGreedy T ⟹ chainGreedy (insert (x+1) T) = chainGreedy T **
isChainFace_insert_succ   ** hence adjoining x+1 to a face of Δ_r keeps it a face **
```

The induction splits on whether `x` is the first greedy element: if it is, `x+1` fails the filter
and disappears; if not, `x+1` survives the filter and the hypothesis applies to the smaller set.

This is exactly shape II of the reduction: in the recursion the forced set has just taken `k` and
the least available vertex is `k+1`, so that vertex can be adjoined to every face — it is a cone
point, `exists_isRegular_cone` applies, and no shedding is needed at that step.

`HTGeometry/ChainGreedyLeft.lean` connects the two halves:

```text
chainGreedy_subset_union_of_lt   A entirely left of S ⟹ chainGreedy A ⊆ chainGreedy (A ∪ S)
mem_chainGreedy_union_of_lt      a greedy element of A stays one in A ∪ S
```

The induction is on `A`: the minimum of `A ∪ S` is that of `A`, both filters split as a union, and
the filtered `A` is still left of the filtered `S`.

In the recursion the forced set is left of the available set, so the vertex the greedy last took
inside the forced set is still a greedy element of any face together with the forced set — which is
exactly the hypothesis of `isChainFace_insert_succ`.  Shape II's cone property is therefore
available at every stage of the recursion, not only in the abstract.

`HTGeometry/ChainGreedyAdditive.lean` gives shape I its structure:

```text
chainGreedy_union_of_sep       ** A left of S, every greedy element of A at distance ≥ 2 from S
                                  ⟹ chainGreedy (A ∪ S) = chainGreedy A ∪ chainGreedy S **
card_chainGreedy_union_of_sep  hence the counts add
```

This is the additivity `γ(S ∪ A) = γ(A) + γ(S)`: when the least available vertex is at distance at
least two from the last forced greedy element, the complex on the available vertices is a plain
chain complex with parameter `r − γ(A)` — which is shape I.  With `ChainGreedySucc.lean` (shape II)
and `ChainGreedyLeft.lean` (the hypothesis that supplies it), both shapes of the reduction are now
identified in Lean.

What is left on this card is the double induction on `(N − k, r')` itself, assembling
`exists_isRegular_cone` and `exists_isRegular_shedding` over these identifications, and the transfer
to the secant ring.

### The exact statement that remains to be proved

Everything is in place to type the induction.  The target, in the vocabulary of the modules above:

```text
theorem exists_isRegular_chainForcedOn
    (K : Type u) [Field K] (N r : ℕ) (𝔪 : Ideal (MvPolynomial (Fin N) K))
    (h𝔪 : ∀ i : Fin N, (X i : MvPolynomial (Fin N) K) ∈ 𝔪)
    (A : Finset (Fin N)) (k : ℕ)
    (hleft : ∀ a ∈ A, (a : ℕ) < k)                          -- A is left of the available set
    (hsep  : ∀ x ∈ chainGreedy (A.image Fin.val), x + 2 ≤ k) -- and separated from it
    (hA    : (chainGreedy (A.image Fin.val)).card ≤ r) :
    ∃ rs : List (MvPolynomial (Fin N) K),
      rs.length = min (N - k) (2 * (r - (chainGreedy (A.image Fin.val)).card)) ∧
      (∀ p ∈ rs, p ∈ 𝔪) ∧
      RingTheory.Sequence.IsRegular
        (MvPolynomial (Fin N) K ⧸
          faceFamilyIdeal K (chainForcedOn N r A (intervalFinset N k (N - k)))) rs
```

by strong induction on `N - k`, with three cases:

* `N - k ≤ 2 r'` — every subset of the interval is a face (`isChainFace_intervalFinset`), so the
  complex is a simplex, the ideal is `⊥`, and the sequence is the variables themselves
  (`isRingRegularSeq_finRange_X`, as in `isCohenMacaulayRing_hankelSecantQuotient_of_le`);
* `k` separated from the forced greedy end by exactly one — shape II: `k` is a cone point
  (`isChainFace_insert_succ` with `mem_chainGreedy_union_of_lt`), apply `exists_isRegular_cone` and
  recurse on `k + 1`;
* otherwise — shape I: apply `exists_isRegular_shedding` at `k`, with the deletion given by
  `faceDeletion_chainForcedOn` (recurse on `k+1`, same `A`) and the link by
  `faceLink_chainForcedOn` (recurse on `k+1`, forced set `insert k A`, whose greedy count is one
  larger by `chainGreedy_union_of_sep`).

The four `smul_lt` side conditions are `𝔪 • ⊤ < ⊤` for each of the four quotients, which holds
because `𝔪` is the irrelevant ideal and each ideal is proper
(`faceFamilyIdeal_faceDeletion_ne_top` and its analogues).

Then `chainForcedOn_univ` and `chainForcedFamily_empty` specialise `A = ∅`, `k = 0` to the chain
complex `Δ_r`, `finiteHankelChainIdeal_eq_inf` identifies its Stanley–Reisner ideal with the initial
ideal of the Hankel secant ideal, and `hankelDegenerationLinearEquiv` with
`isHomogeneous_standardForm` carry the conclusion to the secant ring.

**The side conditions are discharged.**  `HTGeometry/IrrelevantSideCondition.lean`:

```text
smul_top_lt_top_quotient      I ≤ 𝔪 and 𝔪 ≠ ⊤  ⟹  𝔪 • ⊤ < ⊤ in R ⧸ I
irrelevantIdeal K σ           the ideal generated by the variables
irrelevantIdeal_ne_top        it is proper (constant coefficient)
faceFamilyIdeal_le_irrelevant every Stanley–Reisner ideal of a nonempty family sits inside it
smul_top_lt_top_faceFamily    ** the side condition for a Stanley–Reisner ring **
```

So the four `smul_lt` hypotheses of `exists_isRegular_shedding` are all instances of one lemma, and
the statement written out above needs no side conditions beyond `F.Nonempty` at each stage.  What
remains is the induction itself and the transfer.

### Correction to the dimension formula in the induction statement

The statement written out above carries `rs.length = min (N − k) (2 * (r − γ(A)))`.  That is right
only in shape I.  Tracing the greedy through shape II shows the formula must carry an extra unit
there:

```text
k ≥ m + 2  (shape I) :   dim = min (N − k) (2 (r − γ(A)))
k = m + 1  (shape II):   dim = 1 + min (N − k − 1) (2 (r − γ(A)))
```

because in shape II the vertex `k` is *free* — the greedy skips it, so it lies in every maximal face
without consuming any of the budget `r − γ(A)`.  That is the same fact that makes `k` a cone point,
seen on dimensions rather than on faces.

So the induction statement must either carry the flag `e = if k = m + 1 then 1 else 0` and read
`dim = min (N − k) (e + 2 (r − γ(A)))`, or be split into two mutually recursive statements, one per
shape.  The second is probably cleaner in Lean: shape II reduces to shape I in one cone step
(`exists_isRegular_cone` with `isChainFace_insert_succ`), and shape I reduces to shape I and shape II
in one shedding step (`exists_isRegular_shedding`).

Everything else in the plan stands.  This correction is recorded because the earlier entry stated the
uniform formula, which would have produced an unprovable goal.

### The two-shape induction, with its arithmetic verified

Write `g = γ(A)` and `d = r − g` for the remaining budget.  The two statements are

```text
P_I  (A, k) :  ∃ rs of length  min (N−k) (2d)        regular on K[Δ^{A,[k,N)}]
P_II (A, k) :  ∃ rs of length  1 + min (N−k−1) (2d)  regular on K[Δ^{A,[k,N)}]
```

with `P_I` under the separation `∀ x ∈ chainGreedy A, x + 2 ≤ k` and `P_II` under `∃ x ∈
chainGreedy A, x + 1 = k`.

*`P_II` from `P_I`.*  `k` is a cone point (`isChainFace_insert_succ`, whose hypothesis comes from
`mem_chainGreedy_union_of_lt`), and its deletion is `Δ^{A,[k+1,N)}`, which satisfies the separation
at `k+1` because the largest greedy element `x` of `A` has `x + 2 = k + 1`.  So
`exists_isRegular_cone` turns `P_I (A, k+1)` into `P_II (A, k)`, and the lengths match by
construction.

*`P_I` base case, `N − k ≤ 2d`.*  Additivity gives `γ(S ∪ A) = g + γ(S) ≤ g + ⌈(N−k)/2⌉ ≤ r` for
every `S ⊆ [k,N)`, so every subset is a face: the Stanley–Reisner ideal is the coordinate ideal of
the complement of `[k,N)`, the quotient is a polynomial ring on `N − k` variables, and those
variables are the sequence.  Its length `N − k` is `min (N−k) (2d)`.

*`P_I` step, `N − k > 2d`.*  Shed at `k` with `exists_isRegular_shedding`:

```text
deletion :  Δ^{A,[k+1,N)}        shape I,  length min (N−k−1) (2d)   = 2d
link     :  Δ^{A ∪ {k},[k+1,N)}  shape II, length 1 + min (N−k−2) (2d−2) = 2d−1
```

and `exists_isRegular_shedding` wants exactly `n₀ + 1 = 2d` for the deletion and `n₀ = 2d − 1` for
the link.  **The arities match**, which is the check that the whole scheme is consistent; both
equalities use `N − k > 2d`.

So the remaining Lean work is these two statements by strong induction on `N − k`, plus the simplex
base case identification, plus the transfer to the secant ring.

**The base case is proved.**  `HTGeometry/ChainSimplexBase.lean`:

```text
faceFamilyIdeal_powerset            ** the ideal of a simplex is the coordinate ideal of the
                                       complement **
chainForcedOn_eq_powerset_of_short  ** N − k ≤ 2(r − γ(A)) ⟹ the complex is a simplex **
ringKrullDim_faceFamilyIdeal_powerset   its dimension is the number of vertices
```

The short case uses `card_chainGreedy_union_of_sep` for `γ(S ∪ A) = γ(A) + γ(S)` and
`card_le_of_pairwise_chainAdj_interval` to bound `γ(S) ≤ r − γ(A)`; with
`quotientSpanXImageEquiv` the quotient is the polynomial ring on the available variables, whose
regular sequence is those variables.

Of the two-shape induction, the base case, both recursion steps, both shape identifications, the
dimension inputs and the side conditions are now proved.  What is left is the induction itself and
the transfer to the secant ring.

`HTGeometry/CoordinateVariableRegular.lean` turns the simplex base case into an actual sequence:

```text
X_notMem_span_X_image        v ∉ S ⟹ X v ∉ span (X '' S)
isRegularOn_X_span_X_image   ** X v is a nonzerodivisor modulo span (X '' S) **
```

both straight from `mem_ideal_span_X_image` and `isPrime_span_X_image`.  Modulo the coordinate ideal
of the complement, the available variables are successively regular, because at each stage the ideal
generated so far is again a coordinate ideal not containing the next variable — so the base case's
regular sequence exists and has the length the induction wants.

### The induction is proved — the degeneration is Cohen–Macaulay for every `r`

`HTGeometry/QuotientRegularSequence.lean` unwinds what a regular sequence on a quotient ring is:

```text
isSMulRegular_congr                 regularity transports along a linear equivalence
quotSMulTopIdealEquiv               ** (R ⧸ I) ⧸ (J • ⊤) ≃ₗ[R] R ⧸ (I ⊔ J) **
isRegular_quotient_of_isRegularOn   ** hence the criterion, entry by entry **
isRegular_map_X                     variables outside a coordinate ideal are regular on its quotient
isRegular_powerset                  ** the simplex base case, with its variables **
```

`HTGeometry/ChainShapeInduction.lean` then runs the two-shape induction itself:

```text
HasRegSeq                    a regular sequence of a given length inside the irrelevant ideal
chainGreedy_insert_of_sep    γ(A ∪ {k}) = γ(A) ∪ {k} when k is separated from the greedy end
isConePoint_chainForcedOn    ** a vertex one past the greedy end of the forced set is a cone point **
hasRegSeq_base               short interval: the complex is a simplex, its variables are the sequence
hasRegSeq_zero               exhausted budget: the empty sequence
hasRegSeq_shapeI             ** min (N − k) (2 (r − γ(A))) by strong induction on N − k **
```

Both shapes appear exactly as designed: shedding at `k` produces the deletion (shape I on `[k+1,N)`,
length `2d`) and the link (shape II on `[k+1,N)`, length `2d − 1`), and shape II is a cone over
shape I on `[k+2,N)` because `k+1` sits one past the greedy end of `A ∪ {k}`.

`HTGeometry/ChainDegenerationCohenMacaulay.lean` transfers the sequence into the quotient ring and
concludes:

```text
isRegularOn_map_mk_iff                        regularity of the image modulo the image ideal
isRingRegularSeq_map_mk                       ** the images form a ring-regular sequence **
isCohenMacaulayRing_of_isRegular_quotient     length = dimension gives Cohen–Macaulayness
hasRegSeq_chainFaceFinset                     the chain complex, at A = ∅ and k = 0
isCohenMacaulayRing_finiteHankelChainQuotient ** the degeneration is Cohen–Macaulay, all r **
```

for every `N` and `r` with `2r ≤ N`, unconditionally, with axioms `[propext, Classical.choice,
Quot.sound]`.

**What remains on this card** is only the Gröbner-degeneration transfer: `depth (R/I) ≥ depth
(R/in(I))`, which upgrades the Cohen–Macaulayness just proved for the initial ideal to the secant
ideal itself.  The corpus already owns the two ingredients that make the initial ideal the right
one (`finiteHankelSecant_degLex_isGroebnerBasis`, and the shared standard-monomial complement
`isCompl_finiteHankelSecantIdeal_standardSpan` / `isCompl_finiteHankelChainIdeal_standardSpan`).
The transfer itself is the flat family over `K[t]` with special fibre `R/in(I)` and generic fibre
`R/I`, plus semicontinuity of depth.

Two shortcuts that do **not** work, checked here so they are not retried:

* *Replacing the sequence by its initial forms.*  For a monomial ideal `J` and `m` regular mod `J`,
  `in(m)` need not be regular mod `J`: `m ∉ P` for a monomial prime `P` says every term of `m`
  avoids `P`, which is strictly stronger than `in(m) ∉ P`.
* *Using the standard-monomial linear equivalence.*  `hankelDegenerationLinearEquiv` is an
  isomorphism of `K`-vector spaces, not of rings, so it moves Hilbert functions but not depth.

### The degeneration engine, and why the transfer needs the family and not just initial forms

`HTGeometry/InitialIdealDegeneration.lean` builds the weight degeneration from the ground up:

```text
lowestForm_mul                            ** the lowest-weight forms multiply **
initialFormSet, initialIdeal              the initial ideal, realised as the K-span of the forms
exists_lowestForm_eq_of_mem_initialIdeal  ** a nonzero homogeneous element of it is an initial form **
exists_lowestForm_notMem_initialIdeal     ** every class outside I has a representative whose
                                             lowest form escapes the initial ideal **
isRegularOn_of_isRegularOn_lowestForm     ** in(f) regular mod in(I) ⟹ f regular mod I **
```

Taking the span over `K` rather than over the polynomial ring is what makes the ideal weight-graded,
and that grading is what turns a homogeneous element of it back into an initial form; multiplying a
lowest form by a monomial gives a lowest form, so the `K`-span is already an ideal.  For nonpositive
weights the minimal weight of a nonzero polynomial is bounded above by zero, so the reduction
terminates.

**This does not by itself finish the card, and the reason is worth recording.**  Descent of
regularity consumes a regular sequence *of initial forms* on `R/in(I)`.  Initial forms are
`w`-homogeneous, and for a weight separating the Hankel variables the `w`-homogeneous polynomials
are essentially the monomials — while on a Stanley–Reisner ring that is not a cone *no* monomial is
regular, since a variable is regular exactly at a cone point.  So the chain complex admits no
regular sequence of initial forms at all, and the homogeneous-lifting route is closed.

The flat family avoids this precisely because the extra variable `t` supplies the missing freedom:
the sequence is lifted from the special fibre by arbitrary lifts, with the `t`-adic filtration, not
the weight grading, driving the induction.  So the remaining work on this card is

```text
A = K[t][x]/Ĩ      free over K[t] with the standard monomials as basis      (Macaulay basis)
A/tA ≅ R/in(I)     the special fibre
A/(t−1)A ≅ R/I     the generic fibre
lifting            a regular sequence on A/tA is regular on A, hence on A/(t−1)A
```

and the first of these is exactly the reduction argument proved above, run over `K[t]`.

### The family: homogenization is built

`HTGeometry/WeightHomogenization.lean` writes the weight filtration out in a new variable:

```text
weightSub              the substitution x i ↦ T ^ w i * x i, into Laurent polynomials
toLaurent_homogenize   ** toLaurent (homogenize f) = T ^ (-minWeight f) * weightSub f **
homogenize             the homogenization itself, a polynomial in the new variable
homogenize_coeff_zero  ** the special fibre: its constant term is the lowest form **
homogenize_eval_one    ** the generic fibre: its value at one is the polynomial **
homogenize_mul         ** homogenization is multiplicative **
```

Multiplicativity is the step that would be painful by hand — it needs the graded product formula for
weighted components — and the Laurent picture removes it entirely: the substitution `x i ↦ T ^ w i ·
x i` is a ring homomorphism, homogenization is that substitution scaled by `T ^ (-minWeight)`, and
`minWeight` is additive, so multiplicativity follows from the injectivity of `Polynomial.toLaurent`.

With this the family's coordinate ring is available: `Ĩ` generated by the homogenizations of `I`,
with `Ĩ + (t) ↦ in(I)` and `Ĩ + (t−1) ↦ I`.  What remains is the freeness of `K[t][x]/Ĩ` over `K[t]`
(the reduction argument of `InitialIdealDegeneration` run over `K[t]`), the lifting of a regular
sequence across `t` (which needs only `t`-adic separatedness, and the weight grading with `t` of
weight `−1` supplies that), and the specialisation at `t = 1`.

### Lifting across `t`, and the exact obstruction to iterating it

`HTGeometry/RegularLiftingAcrossT.lean`:

```text
isSMulRegular_of_isSMulRegular_quotient
    ** t regular, M t-separated, x regular on M ⧸ tM ⟹ x regular on M **
isSMulRegular_quotient_of_isSMulRegular_quotient
    ** t regular on M and x regular on M ⧸ tM ⟹ t regular on M ⧸ xM **
```

The first is a descent — anything killed by `x` is divisible by `t`, and dividing preserves being
killed by `x`, so it is divisible by every power of `t` and hence zero.  The second is what lets the
first be applied again after passing to `M ⧸ xM`.

**The obstruction to iterating is now pinned down with a counterexample.**  Separatedness is *not*
inherited by `M ⧸ xM`: over `M = K[t]` with `x = 1 − t`, `M` is `t`-separated and `x` is regular on
`M ⧸ tM = K`, yet `M ⧸ xM ≅ K` has `t` acting as the identity, so every power of `t` is surjective
on it.  So a sequence cannot be lifted by naive iteration; each stage needs its own separatedness
input.

In the family this is supplied by the grading: `Ĩ` is homogeneous for the weight that gives `t`
weight `−1` and every `x` variable a nonpositive weight, so a nonzero element has components in
degrees bounded above and cannot lie in `t^n · A` for large `n`.  What the grading does *not* supply
is separatedness of `A ⧸ (u₁,…,u_i)A` for a non-homogeneous sequence — which is exactly why the
textbook proof of the transfer runs through semicontinuity of depth in the flat family rather than
through a naive lift, and why the specialisation at `t = 1` is the step that still needs the graded
local-cohomology comparison.

### The grading of the family, and the structure theorem behind `t`-saturation

`HTGeometry/WeightGradedFamily.lean` gives the extra variable weight `−1` and grades the family:

```text
weightedHomogeneousComponent_mul_right   multiplying by a homogeneous polynomial shifts components
homogenize_coeff                         the coefficients of the homogenization are the components
IsFamHomog, isFamHomog_homogenize        homogenization is homogeneous, of weight its minimal weight
weightedHomogeneousComponent_eval_one    ** the components of the dehomogenization are exactly the
                                            coefficients **
eq_X_pow_mul_homogenize                  ** a homogeneous polynomial is t^k times the homogenization
                                            of its dehomogenization **
```

The structure theorem is the crux.  Homogeneity forces the coefficients into distinct weights, so the
dehomogenization remembers all of them; its minimal weight is attained at the trailing coefficient,
and dividing by that power of `t` returns the homogenization on the nose.  This is precisely the
shape needed for `t`-saturation: if `t·F` lies in the family ideal then, decomposing `F` into
homogeneous parts and writing each as `t^k · (its dehomogenization)^h`, the dehomogenization lies in
`I` and hence `F` lies in the family ideal.  `weightedHomogeneousComponent_mul_right` is the missing
mathlib lemma that makes the family ideal homogeneous in the first place.

### The family is saturated — the flatness of the degeneration is proved

`HTGeometry/FlatFamilyIdeal.lean`:

```text
famComp, famComp_coeff              the weight-d part of a polynomial in the extra variable
sum_famComp                         ** a polynomial is the sum of its homogeneous parts **
famComp_mul_left_of_isFamHomog      multiplying by a homogeneous polynomial shifts the parts
familyIdeal                         generated by the homogenizations of the elements of I
mem_familyIdeal_iff                 ** membership is part-by-part: F is in the family ideal exactly
                                       when every homogeneous part of F dehomogenizes into I **
familyIdeal_saturated               ** the family ideal is saturated in the extra variable **
```

The part-by-part criterion is the workhorse.  One direction is a span induction whose only
interesting case is a product, handled by decomposing the multiplier into homogeneous parts and
applying the shift; the other is the structure theorem, which writes a homogeneous element as a
power of `t` times the homogenization of its dehomogenization.

Saturation then falls out in three lines: multiplying by `t` shifts the parts by one and leaves
their dehomogenizations untouched.  **This is the torsion-freeness of `K[t][x]/Ĩ` over `K[t]` — the
flatness of the degeneration**, and it is the first of the three items this card still needed.

What remains: the two fibres (`Ĩ + (t)` against the initial ideal, `Ĩ + (t−1)` against `I`), and the
specialisation at `t = 1`, which is where the graded comparison is still owed — the lifting lemma
alone does not suffice, for the reason recorded above.

### Both fibres are proved

`HTGeometry/FlatFamilyFibres.lean`:

```text
familyIdeal_sup_X_sub_one   ** modulo t − 1 the family ideal is the ideal itself **
familyIdeal_sup_X           ** modulo t it is the initial ideal **
```

Each is one of the two evaluations of the homogenization turned into an ideal statement: a
homogenization differs from the constant `f` by a multiple of `t − 1` because evaluating at one
returns `f`, and from the constant `lowestForm f` by a multiple of `t` because its constant
coefficient is the lowest form.  The reverse inclusions run the same identities backwards, using for
the special fibre that the initial ideal is the `K`-span of the initial forms, so a span induction
reduces to a single generator.

**The flat family is now complete**: `familyIdeal_saturated` (torsion-free over the base line),
`familyIdeal_sup_X` (special fibre = initial degeneration), `familyIdeal_sup_X_sub_one` (generic
fibre = the ideal).  Of the three items this card still owed, two are done; what is left is the
specialisation of *depth* at `t = 1`, which the counterexample recorded above shows cannot be
obtained by iterating the lifting lemma and needs the graded comparison instead.

### The specialisation argument, written out — and the one mathlib gap it needs

`HTGeometry/FamilyNoPositiveWeight.lean` proves the two graded facts at ring level:

```text
famComp_eq_zero_of_pos          the homogeneous parts vanish above weight zero
familyIdeal_sub_one_saturated   ** the family ring has no (t−1)-torsion **
familyIdeal_separated           ** and it is separated for t **
```

Both are the same downward sweep: multiplying by `t − 1` shifts the parts by one and subtracts, so
the dehomogenizations satisfy a difference relation that starts at zero in positive weight and
propagates downwards; multiplying by `t^n` shifts by `n`, so a part in weight `d` is untouched by
the correction once `n` exceeds `−d`.

**The full specialisation argument is this, and it is sharp** (write `k = A/𝔪A`, `n` for the depth of
the special fibre):

1. `Ext^i(k, A/tA) = 0` for `i < n` — Rees, from the special fibre's depth, which this card proves.
2. The long exact sequence of `0 → A --t--> A → A/tA → 0` makes `Ext^i(k, A)` `t`-divisible for
   `i < n`; a weight-graded module with weights bounded above and `E = tE` is zero, so
   `Ext^i(k, A) = 0` for `i < n`.
3. The long exact sequence of `0 → A --(t−1)--> A → A/(t−1)A → 0` puts `Ext^i(k, A/(t−1)A)` between
   `Ext^i(k, A) = 0` and the `(t−1)`-kernel of `Ext^{i+1}(k, A)`.  At `i + 1 < n` that kernel is
   zero; at `i + 1 = n` it is zero because **`t − 1` acts injectively on a graded module with
   weights bounded above** — kill the top component.  So `Ext^i(k, R/I) = 0` for `i < n`.
4. Rees again: `depth(R/I) ≥ n`, hence `R/I` is Cohen–Macaulay.

Step 3's injectivity trick is what makes the argument lose nothing; the naive bookkeeping gives only
`n − 1`.  Steps 2 and 3 are exactly the two facts just proved at ring level, but they are needed for
`Ext` modules, and **mathlib's `Ext` does not carry a grading**.  That is the single remaining gap
on this card: a weight-graded `Ext` (equivalently, Koszul homology of the variables, which is
manifestly graded since the variables are homogeneous — mathlib has no Koszul complex either).

### A route to the last step that needs no graded `Ext` at all

The graded-`Ext` gap can be sidestepped.  The specialisation can be run with *explicit* sequences
provided the regular sequence on the special fibre is taken **standard-homogeneous** — and over an
infinite field it can even be taken **linear**.  The chain, with each link elementary:

```text
(A)  x is regular on M  ↔  x avoids every associated prime            (mathlib:
     biUnion_associatedPrimes_eq_compl_regular, associatedPrimes.finite)
(B)  depth ≥ 1 ⟹ no associated prime contains the degree-one part, so each meets it in a proper
     subspace; over an infinite field a finite union of proper subspaces misses a point, so a
     LINEAR form is regular
(C)  iterating (B) gives a regular sequence of linear forms of length the depth
(D)  with the u's linear, A ⧸ (u₁,…,u_i)A stays graded by x-degree with pieces finitely generated
     over K[t]; t-regularity (isSMulRegular_quotient_of_isSMulRegular_quotient) makes those pieces
     torsion-free, hence free over the PID K[t], hence
       * t-separated — so the lift isSMulRegular_of_isSMulRegular_quotient applies at every stage,
       * (t−1)-regular — because (t−1) is regular on a free K[t]-module
(E)  and then two-element permutation closes it:  u a = (t−1) b  with (t−1) regular mod u gives
     b = u c, so u (a − (t−1) c) = 0, so a = (t−1) c.  Hence u is regular on A ⧸ (t−1)A = R/I
(F)  finally, CM is insensitive to enlarging K, which handles a finite base field
```

Every ingredient of (D) and (E) is already in the corpus: `isSMulRegular_of_isSMulRegular_quotient`,
`isSMulRegular_quotient_of_isSMulRegular_quotient`, `familyIdeal_saturated`,
`familyIdeal_separated`, `familyIdeal_sub_one_saturated`, and both fibres.  What is missing is (B)'s
vector-space input — *a vector space over an infinite field is not a finite union of proper
subspaces* — and the bookkeeping of (D).

This replaces "build graded `Ext`" (a mathlib-scale project) with a short, self-contained list.  The
`t − 1` counterexample recorded earlier is not violated: there the element `1 − t` is not in the
irrelevant ideal, whereas here every `u_i` is.

### Step (B) is proved: a linear nonzerodivisor exists

`HTGeometry/LinearNonzerodivisor.lean`:

```text
subsingleton_line_meet           a line meets a subspace missing its base point at most once
exists_notMem_of_finite_proper   ** a vector space over an infinite field is not a finite union of
                                    proper subspaces **
linearForm, linearFormMap        the linear form with given coefficients
exists_linearForm_isSMulRegular  ** if some element of the irrelevant ideal is a nonzerodivisor then
                                    a linear form is **
```

The subspace lemma is the line argument: given a point outside all but one subspace, slide along a
direction outside the last one; each earlier subspace catches the moving point at most once, and an
infinite field has room to avoid finitely many values.  The application uses mathlib's
`biUnion_associatedPrimes_eq_compl_regular` and `associatedPrimes.finite`: no associated prime
contains the regular element, hence none contains the irrelevant ideal, hence none contains every
variable, so the coefficient vectors each one catches form a proper subspace and a vector escapes
them all.

This is step (B) of the route above.  With it the special fibre's regular sequence can be taken to
consist of linear forms — which is exactly the homogeneity the family bookkeeping (D) needs, and the
reason the graded-`Ext` gap can be bypassed.

### Step (C)'s engine: depth drops by exactly one across a regular element

`HTGeometry/RegularElementDepthDrop.lean` supplies the third end of the depth transfer, which the
corpus did not have (it had the sub- and middle-object versions only):

```text
subsingleton_ext_quotient_of_shortExact
    ** Ext^n(X,B) and Ext^{n+1}(X,A) vanishing forces Ext^n(X,C) to vanish **
smulShortComplex, smulShortComplex_shortExact
    the sequence 0 → M → M → M ⧸ uM → 0 of a nonzerodivisor
subsingleton_ext_quotSMul
    ** Ext-vanishing below n+1 on M gives Ext-vanishing below n on M ⧸ uM **
```

Read through Rees, the last statement says quotienting by a regular element drops the depth by at
most one.  Combined with `exists_linearForm_isSMulRegular` this is the induction step of (C): take a
linear nonzerodivisor, pass to the quotient, and repeat — producing a regular sequence of **linear
forms** of length the depth, which is the homogeneity the family bookkeeping needs.

### Step (C) is proved: the sequence can be taken linear

`HTGeometry/LinearRegularSequence.lean`:

```text
map_smul_top                    the image of I • ⊤ under a quotient map is I • ⊤
smul_top_lt_top_quotSMul        properness survives quotienting by an element of the ideal
linearForm_mem_irrelevantIdeal
exists_linear_isRegular         ** a regular sequence of length n inside the irrelevant ideal gives
                                   a LINEAR one of the same length **
```

The induction is the expected one and both inputs are now in place: a linear nonzerodivisor exists
(`exists_linearForm_isSMulRegular`), and quotienting by it drops the depth by exactly one
(`subsingleton_ext_quotSMul`), so Rees converts back and forth at each step.  The properness side
condition is graded Nakayama: if the irrelevant ideal were everything on the quotient it would be
everything upstairs, since the element quotiented by already lies in it.

**Steps (A), (B), (C) and (E) of the route are now done** — (E) is
`isSMulRegular_quotient_of_isSMulRegular_quotient`, already proved: with `u` regular on `A` and
`t − 1` regular on `A ⧸ uA` it returns `u` regular on `A ⧸ (t−1)A = R/I`, which is exactly the
two-element permutation.  What is left is (D): that `A ⧸ (u₁,…,u_i)A` has `x`-graded pieces finitely
generated over `K[t]`, so that `t`-regularity makes them free and hence both `t`-separated and
`(t−1)`-regular.

### Step (D) begins: the family's second grading

`HTGeometry/FamilyXGrading.lean` puts the standard grading on the family, with the extra variable in
degree zero:

```text
xComp, xComp_coeff             the x-degree-e part
IsXHomog, isXHomog_xComp       homogeneity for the x-degree
xComp_eq_self_of_isXHomog
sum_xComp                      ** a polynomial is the sum of its x-homogeneous parts **
```

plus the standard-degree analogues of the weighted decomposition lemmas and the identity
`weight_one_eq_degree` between the all-ones weight and the total degree.

The two gradings play different roles.  The **weight** grading, where `t` has weight `−1`, controls
the degeneration and gave `familyIdeal_saturated`, `familyIdeal_separated` and
`familyIdeal_sub_one_saturated`.  The **x**-grading, where `t` has degree `0`, is the one that
survives quotienting by *linear* forms — which is why step (C) had to produce a linear sequence — and
it is what makes the graded pieces finitely generated modules over `K[t]`, hence free once
`t`-torsion-free, hence both `t`-separated and `(t−1)`-regular.

### Correction: step (D) as stated does not close, and why

The route above is right in outline but **step (D) is not justified as written**, and the gap is
worth stating precisely so it is not re-attempted.

(D) asked that `A ⧸ u₁A` be `(t−1)`-regular, deduced from its `x`-graded pieces being finitely
generated and `t`-torsion-free over `K[t]`.  Finitely generated plus `t`-torsion-free does **not**
give free over `K[t]`: `K[t]/(t−1)` is finitely generated and `t`-torsion-free while `t − 1` kills
it.  Excluding torsion at `(t−1)` is exactly the statement that the generic fibre is no worse than
the special one — the semicontinuity being proved.  So (D) is circular.

Two repairs that also fail, recorded:

* *Quotient by the homogenization `u₁^h` instead of `u₁`.*  Then the ideal stays weight-homogeneous
  and the sweep does give `(t−1)`-torsion-freeness — but the special fibre becomes
  `R/(in(I) + in(u₁))`, so the induction now needs `in(u₁)` to be regular on `R/in(I)`, which is the
  original obstruction.
* *A weight-homogeneous regular sequence inside `A`.*  By `eq_X_pow_mul_homogenize` every
  weight-homogeneous element of the family is `t^k` times a homogenization, so its image on the
  special fibre is an initial form or zero — the same obstruction again.

**What does close it** is the Koszul route, and there the grading is concrete rather than abstract:

```text
A is x-graded with pieces finitely generated and torsion-free over K[t], hence FREE
K(x₁,…,x_N; A) is a complex of graded free K[t]-modules, and it is weight-graded too, because the
    variables are weight-homogeneous
universal coefficients over the PID K[t]:
    0 → H_i ⊗ κ → H_i(C ⊗ κ) → Tor₁(H_{i−1}, κ) → 0
at t = 0 the middle vanishes above N − n (special fibre depth), so H_i = t·H_i, and a weight-graded
    module with weights bounded above and H = tH is zero
hence H_i = 0 above N − n, hence the same at t = 1, hence depth(R/I) ≥ n
```

The Nakayama step is the one that fails for the `x`-grading (where `t` has degree zero) and works for
the weight grading (where `t` has weight `−1`) — the same asymmetry that has driven this whole
argument.  What is missing is the Koszul complex itself and its depth sensitivity; mathlib has
neither.  Unlike `Ext`, though, Koszul homology carries the weight grading by construction, so this
is a self-contained build rather than a modification of mathlib's `Ext`.

### The family is torsion-free over the base line

`HTGeometry/FamilyTorsionFree.lean`:

```text
isFamHomog_monomial_C                          a scalar monomial in t is weight-homogeneous
familyIdeal_saturated_of_coeff_zero_ne_zero    ** a scalar polynomial with nonzero constant term
                                                  does not divide into the family ideal **
```

The downward sweep once more: multiplying by `t^k` shifts the homogeneous parts by `k`, so a scalar
polynomial `q` turns the dehomogenizations `a_d` into the relations `∑_k q_k · a_{d+k} ∈ I`; above
weight zero every `a_d` vanishes and the constant term of `q` is an invertible scalar, so the
relations determine the `a_d` downwards.

With `familyIdeal_saturated` (the case `q = t`) this is torsion-freeness for **every** nonzero scalar
polynomial, since any such factors as a power of `t` times one with nonzero constant term.  That is
what makes each `x`-graded piece of the family a finitely generated torsion-free — hence free —
`K[t]`-module, which is the input the Koszul comparison of the two fibres consumes.

### A second route to the last step, with no homological algebra at all

The Koszul route is not the only way past semicontinuity.  **Hilbert functions suffice**, and the
argument is linear algebra plus the structure of finitely generated modules over `K[t]`:

```text
Hilb(R/I)·(1−z)^n ≤ Hilb(R/(I+ℓ))        quotienting by a form drops each degree by at most the
                                          shifted amount, with EQUALITY iff the form is regular
                  ≤ Hilb(R/(J+ℓ))         semicontinuity in the family
                  = Hilb(R/J)·(1−z)^n     the ℓ's ARE regular on the special fibre (step C)
                  = Hilb(R/I)·(1−z)^n     the two rings have the same Hilbert function
```

so equality holds throughout and the linear forms are a regular sequence on `R/I` — which is
Cohen–Macaulayness.  The first line's equality criterion is now proved:

```text
HTGeometry/DimensionInjectivity.lean
  ker_eq_bot_of_finrank_quotient_range   ** the quotient by the image having the dimension
                                            rank-nullity predicts forces injectivity **
```

The remaining input is the middle inequality.  It is *not* the false statement
`dim V/(t−1)V ≤ dim V/tV` — that fails for `V = K[t]/(t−1)`.  It is the two standard facts about a
finitely generated module over the PID `K[t]`: every fibre has dimension at least the rank, and all
but finitely many have dimension exactly the rank.  Since the substitution `x i ↦ λ^{w i} x i`
carries the fibre at any `λ ≠ 0` isomorphically onto the fibre at `1`, all nonzero fibres have the
same dimension, hence that common value is the rank, hence it is at most the dimension at `t = 0`.

The last equality — equal Hilbert functions — is already owned for this card's pair by
`isCompl_finiteHankelSecantIdeal_standardSpan` and `isCompl_finiteHankelChainIdeal_standardSpan`:
both ideals are complementary to the *same* standard-monomial span.

### All nonzero fibres of the family are the same ring

`HTGeometry/FamilyNonzeroFibres.lean`:

```text
familyWeightScale            the rescaling x i ↦ lam ^ (w i) * x i
familyWeightScale_monomial   its effect on a monomial
eval_homogenize              ** evaluating the homogenization at lam returns the rescaled
                                polynomial, up to an invertible scalar **
```

So the fibre over any nonzero point is the image of the original ideal under an automorphism of the
polynomial ring, hence isomorphic to the fibre over `1`.  This is the second input of the
semicontinuity step, and the reason it can be used at all: a property that holds at *all but finitely
many* points of the base therefore holds at *every* nonzero point, in particular at `t = 1`.

What the Hilbert-function route still needs is the first input — that for a finitely generated
`K[t]`-module every fibre has dimension at least the rank and all but finitely many have dimension
exactly the rank.  Mathlib's structure theorem for finitely generated modules over a principal ideal
domain (`Module.equiv_free_prod_directSum`) gives it: the free part contributes the rank at every
point, and each torsion summand `K[t]/(p^e)` contributes only at the single point where `p` vanishes.

### The torsion half of the fibre count

`HTGeometry/CyclicFibreDimension.lean`:

```text
isMaximal_span_X_sub_C      the ideal of a point is maximal
finrank_quotient_span_pair  ** a cyclic module K[X]/(q) contributes one dimension at the points
                               where q vanishes and none elsewhere **
```

Both cases are short: where `X − lam` divides `q` the sum of the two ideals is the ideal of the
point, whose quotient is the base field; where it does not, the sum strictly contains a maximal ideal
and is therefore everything.

With the free half — every free summand contributes its rank at every point — this gives the
semicontinuity input: fibre dimension equals the rank away from the finitely many points carried by
the torsion.  Mathlib's `Module.equiv_free_prod_directSum` supplies the decomposition into those two
halves, so what remains for this input is the free half and the assembly.

### The free half of the fibre count

`HTGeometry/FreeFibreCoordinates.lean`:

```text
mem_smul_top_finsupp_iff   ** an element of a finite free module lies in I • ⊤ exactly when every
                              coordinate lies in I **
sub_eval_mem_span          modulo the ideal of a point, a polynomial is its value there
C_mem_span_iff             and a constant lies in that ideal only if it is zero
```

The first is the free half of the fibre count: modulo `I` a finite free module has one coordinate per
basis element, so its fibre has the rank as its dimension at *every* point — no exceptional points at
all, which is why only the torsion can raise the fibre dimension.  The other two identify those
coordinates concretely over the base line: division by `X − lam` is evaluation at `lam`, and the
resulting constants are independent.  Together with `finrank_quotient_span_pair` these are both
halves of the semicontinuity input; what remains is to assemble them along
`Module.equiv_free_prod_directSum`.

### The free half, completed

`HTGeometry/FreeFibreDimension.lean`:

```text
fibreBasisFun              the images of the basis vectors
fibre_span                 ** every class is the combination of them given by evaluation **
fibre_linearIndependent    and they are independent, since a constant in the ideal of a point is zero
freeFibreBasis
finrank_quotient_finsupp   ** the fibre of a finite free module has the rank as its dimension, at
                              every point **
```

Division by `X − lam` is evaluation at `lam`, so the coordinates of a class are the values of the
coordinates of any representative — that single fact gives both the spanning and the independence.
There are no exceptional points for a free module, which is exactly why only the torsion of a
finitely generated module can raise the fibre dimension above the rank.

Both halves of the semicontinuity input are now proved:
`finrank_quotient_span_pair` (torsion, one dimension only where the annihilator vanishes) and
`finrank_quotient_finsupp` (free, the rank everywhere).  What remains is to combine them along
`Module.equiv_free_prod_directSum` and feed the result into the Hilbert-function chain.

### Fibres transport and split

`HTGeometry/FibreTransport.lean`:

```text
map_smul_top_of_equiv   an equivalence carries I • ⊤ onto I • ⊤
quotSmulEquivOfEquiv     ** hence the fibre depends only on the isomorphism class **
smul_top_prod            ** and on a product, I • ⊤ is the product of the two I • ⊤ **
```

These are the two bookkeeping steps the fibre count needs before
`Module.equiv_free_prod_directSum` can be applied: the count is invariant under isomorphism, so it
may be computed on the decomposition, and it is additive along a product, so the free part and the
torsion part contribute separately.  With `finrank_quotient_finsupp` (free: the rank at every point)
and `finrank_quotient_span_pair` (torsion: one dimension only where the annihilator vanishes), the
assembly is now a matter of iterating the product step over the finitely many cyclic summands.

### The fibre of a finite product

`HTGeometry/PiFibreSplit.lean`:

```text
single_mem_smul_top   a single coordinate in I • ⊤ gives a vector in I • ⊤
mem_smul_top_pi_iff   ** on a finite product, I • ⊤ is exactly the coordinatewise condition **
piQuotSmulEquiv       ** hence the fibre of a finite product is the product of the fibres **
```

The forward direction is the projection; the reverse writes a vector as the sum of its coordinates,
each a single entry.  With it the quotient map splits and the fibre dimension is additive.

That completes the pieces of the semicontinuity input: transport along isomorphisms
(`quotSmulEquivOfEquiv`), additivity (`piQuotSmulEquiv`), the free contribution
(`finrank_quotient_finsupp`, the rank at every point) and the torsion contribution
(`finrank_quotient_span_pair`, one dimension only where the annihilator vanishes).  Applying
`Module.equiv_free_prod_directSum` to a finitely generated module over `K[t]` and summing gives
"fibre dimension = rank away from finitely many points", which is the middle inequality of the
Hilbert-function chain.

### The fibre of a product

`HTGeometry/ProdFibreSplit.lean`:

```text
prodQuotSmulEquiv   ** the fibre of a product is the product of the fibres **
```

The binary companion of `piQuotSmulEquiv`, proved the same way from `smul_top_prod`.  Together they
give the additivity needed to compute a fibre along `Module.equiv_free_prod_directSum`, whose shape
is exactly a product of a free module with a direct sum of cyclic torsion modules.

The assembly is now a chain of the pieces already proved:

```text
finrank (V ⧸ (X−lam)V)
  = finrank ((free × torsion) ⧸ …)            quotSmulEquivOfEquiv
  = finrank (free ⧸ …) + finrank (torsion ⧸ …) prodQuotSmulEquiv
  = n + ∑ᵢ finrank (K[X]/(pᵢ^eᵢ) ⧸ …)          finrank_quotient_finsupp, piQuotSmulEquiv
  = n + #{i : (X−lam) ∣ pᵢ^eᵢ}                 finrank_quotient_span_pair (via
                                                 quotSMulTopIdealEquiv to match the presentation)
```

so the fibre dimension is at least `n` everywhere and exactly `n` off the finitely many roots — the
semicontinuity the Hilbert-function route consumes.

### The fibre-dimension calculus is complete

`HTGeometry/FibreDimensionCalculus.lean`:

```text
finrank_quot_congr   the fibre dimension is an isomorphism invariant
finrank_quot_prod    it is additive on products
finrank_quot_pi      and on finite products
finrank_quot_cyclic  ** and on a cyclic module it is one exactly where the annihilator vanishes **
```

The cyclic value is `finrank_quotient_span_pair` moved from the ideal presentation
`K[X] ⧸ (span q ⊔ span (X − lam))` to the module presentation
`(K[X] ⧸ span q) ⧸ (span (X − lam) • ⊤)` by `quotSMulTopIdealEquiv`.

With `finrank_quotient_finsupp` for the free part, these four compute the fibre of **any** finitely
generated module over the base line: the rank, plus the number of torsion summands whose annihilator
vanishes at that point.  Reading that off `Module.equiv_free_prod_directSum` gives the two facts the
Hilbert-function route needs — fibre dimension at least the rank everywhere, and exactly the rank off
a finite set — and with `eval_homogenize` (all nonzero fibres isomorphic) the middle inequality of
the chain follows.

### The fibres are finite dimensional

`HTGeometry/FibreFiniteDimensional.lean`:

```text
finiteDimensional_freeFibre          from the basis of the free fibre
finiteDimensional_quotient_X_sub_C   the quotient by the ideal of a point is the base field
finiteDimensional_quotient_sup       so any further quotient of it is finite dimensional
finiteDimensional_cyclicFibre        ** hence so is the fibre of a cyclic module **
```

These are the side conditions the additivity lemmas carry — `finrank` is additive across a product
only when the factors are finite dimensional — and each fibre here is: the free one has an explicit
basis, the cyclic one is a quotient of `K[X] ⧸ (X − lam)`, which is the base field.

Everything the semicontinuity statement needs is now in place: the decomposition
(`Module.equiv_free_prod_directSum`), the transport and additivity (`finrank_quot_congr`,
`finrank_quot_prod`, `finrank_quot_pi`), the two values (`finrank_quotient_finsupp`,
`finrank_quot_cyclic`), and these finiteness side conditions.

### Semicontinuity of the fibre dimension is proved

`HTGeometry/FibreSemicontinuity.lean`:

```text
finrank_fibre_eq            the fibre of a decomposed module is the rank plus the number of torsion
                            summands whose annihilator vanishes at the point
exists_generic_fibre_rank   ** every fibre has dimension at least the rank, and all but finitely
                               many have dimension exactly the rank **
```

The computation reads `Module.equiv_free_prod_directSum` through the fibre calculus: transport to
the decomposed module, split the product, count the free part by its rank and each cyclic part by
whether its annihilator vanishes.  The exceptional set is the roots of the finitely many
annihilators.

**This is the middle inequality of the Hilbert-function chain.**  With `eval_homogenize` — all
nonzero fibres of a weight degeneration are isomorphic — it gives: the dimension at `t = 1` equals
the common nonzero-fibre value, which must be the rank (an infinite field has a point outside the
exceptional set), hence is at most the dimension at `t = 0`.  So

```text
dim (R/(I+ℓ))_e ≤ dim (R/(J+ℓ))_e
```

which is what the chain needed.  What remains for the card is to run the chain itself: equal Hilbert
functions for the pair, the equality criterion `ker_eq_bot_of_finrank_quotient_range` in each degree,
and the conclusion that the linear forms are a regular sequence on `R/I`.

### Regularity is a degreewise condition

`HTGeometry/DegreewiseRegularity.lean`:

```text
homogeneousComponent_mul_left     multiplying by a homogeneous polynomial shifts the components
IsHomogIdeal                      homogeneity of an ideal, stated with the standard components
forall_mem_of_forall_homogeneous  ** a homogeneous element regular on homogeneous elements is
                                     regular **
```

If `l · f` lies in a homogeneous ideal then so does every component of `l · f`, and multiplying by a
homogeneous element shifts components, so each `l · f_e` lies in the ideal; the degreewise hypothesis
puts every `f_e` there, hence `f`.

This is the step that converts a Hilbert-function computation — inherently degreewise — into the
statement that a linear form is a nonzerodivisor.  The chain for this card is now:

```text
semicontinuity (exists_generic_fibre_rank + eval_homogenize)     dim (R/(I+l))_e ≤ dim (R/(J+l))_e
the l's are regular on R/J (exists_linear_isRegular)             dim (R/(J+l))_e = expected
equal Hilbert functions (shared standard-monomial complement)     dim (R/I)_e = dim (R/J)_e
ker_eq_bot_of_finrank_quotient_range                             equality forces injectivity
forall_mem_of_forall_homogeneous                                 degreewise injectivity is
                                                                   regularity
```

with only the third line — the *graded* refinement of the corpus's `isCompl` statements — not yet
in Lean.

### The third link: equal Hilbert functions, degree by degree

`HTGeometry/GradedComplement.lean`:

```text
IsGradedSubmodule       a subspace closed under taking homogeneous components
degreePart              its part in a fixed degree
isCompl_degreePart      ** a complement of graded subspaces is a complement in every degree **
finrank_degreePart_eq   ** hence two graded subspaces with the same complement have the same
                           dimension in every degree **
```

The degreewise complement is read off the global one by taking components: the decomposition of a
homogeneous element into parts in the two subspaces can be replaced by the degree-`e` components of
those parts, which stay in the subspaces because both are graded.

This is exactly the shape of the corpus's pair of `isCompl` statements for this card — the secant
ideal and the chain ideal are both complementary to the *same* standard-monomial span — so their
graded pieces have equal dimensions, and therefore so do the graded pieces of the two quotients.

**All five links of the Hilbert-function chain are now in Lean.**  What remains is to instantiate
them for the Hankel pair: check the two ideals and the standard-monomial span against
`IsGradedSubmodule`, apply `finrank_degreePart_eq`, and run the chain with
`exists_generic_fibre_rank`, `exists_linear_isRegular`,
`ker_eq_bot_of_finrank_quotient_range` and `forall_mem_of_forall_homogeneous`.

### The cokernel identification

`HTGeometry/GradedCokernel.lean`:

```text
mem_sup_span_iff_of_homogeneous  ** a homogeneous element of `a + (l)` splits as α + l·β with both
                                    parts homogeneous **
degreePart_sup_span              ** so in each degree, `a + (l)` is the degree part of `a` plus the
                                    image of multiplication by `l` **
```

The splitting is the component argument: write the element as `α₀ + l·β₀` and take the homogeneous
component of the right degree, which keeps `α₀` in the ideal and turns `l·β₀` into `l` times a
component of `β₀`.

This identifies the cokernel of multiplication — the degree-`(d+e)` piece of the ring modulo
`a + (l)` is the cokernel of `mulDegreeHom` on the pieces modulo `a` — which is precisely what lets
`ker_eq_bot_of_finrank_quotient_range` be applied degree by degree.  With it, the Hilbert-function
equation in a degree says exactly that multiplication by `l` is injective there, and
`forall_mem_of_forall_homogeneous` turns injectivity in all degrees into regularity.

### The Hilbert-function criterion for regularity is proved

`HTGeometry/HilbertRegularityCriterion.lean`:

```text
mulQuotHom             multiplication by `l` between graded pieces of the quotient
range_mulQuotHom       its image
cokerMulQuotEquiv      ** the cokernel is the next graded piece of the ring modulo `a + (l)` **
forall_mem_of_hilbert  ** if the dimensions add up in every degree, `l` is a nonzerodivisor **
```

In each degree, multiplication by a homogeneous element maps one graded piece of `R ⧸ a` to another
and its cokernel is the corresponding piece of `R ⧸ (a + (l))`, so

```text
dim (R/(a+l))_{d+e} + dim (R/a)_e = dim (R/a)_{d+e}
```

is exactly the rank-nullity count for an injective map.  `ker_eq_bot_of_finrank_quotient_range`
turns it into injectivity and `forall_mem_of_forall_homogeneous` assembles the degrees into
regularity.

**This is the engine of the whole route, and it is now unconditional in Lean.**  A Gröbner
degeneration feeds it: the initial ideal supplies the dimensions (its own regular sequence gives the
equation there), the degeneration transports them (`finrank_degreePart_eq` for the ideals,
`exists_generic_fibre_rank` with `eval_homogenize` for the quotients by the form), and regularity
upstairs follows — with no homological algebra anywhere in the argument.

### Both directions of the criterion, and the loop closes

`HTGeometry/HilbertConverse.lean`:

```text
finrank_quotient_range_add_of_injective  an injective map has the predicted cokernel dimension
le_finrank_quotient_range_add            and ANY map has at least that much
hilbert_of_forall_mem                    ** a nonzerodivisor makes the dimensions add up in every
                                            degree **
```

The last is the converse of `forall_mem_of_hilbert`, and it is exactly what the special fibre
supplies: the linear forms *are* a regular sequence on `R/J`, so the Hilbert-function equation holds
there.

**With this the loop closes.**  For a linear form `l` from the special fibre's sequence and each
degree `e`:

```text
dim (R/(I+l))_{1+e} + dim (R/I)_e ≤ dim (R/(J+l))_{1+e} + dim (R/J)_e   semicontinuity + equal
                                                                          Hilbert functions
                                  = dim (R/J)_{1+e}                       hilbert_of_forall_mem
                                  = dim (R/I)_{1+e}                       equal Hilbert functions
```

while `le_finrank_quotient_range_add` gives `≥` unconditionally.  So the equation holds for `I`, and
`forall_mem_of_hilbert` makes `l` a nonzerodivisor on `R/I`.  Iterating over the sequence gives a
regular sequence of length `2r` on the secant ring, which is its Krull dimension — Cohen–Macaulay.

Everything in that display is now a named Lean theorem except the instantiation for the Hankel pair:
checking `IsHomogIdeal` for the two ideals, `IsGradedSubmodule` for the standard-monomial span, and
feeding the corpus's two `isCompl` statements into `finrank_degreePart_eq`.

### The degeneration theorem itself is proved

`HTGeometry/DegenerationTransport.lean`:

```text
forall_mem_of_degeneration   ** if two homogeneous ideals have the same graded complement, and a
                                homogeneous element is regular on one of them with no jump in the
                                fibre dimensions, then it is regular on the other **
```

The proof is the closed loop: equal complements give equal Hilbert functions in every degree; the
regular element gives the Hilbert-function equation for the second ideal; the fibre-dimension bound
transports it to the first as an inequality; `le_finrank_quotient_range_add` supplies the reverse
inequality for free; and `forall_mem_of_hilbert` converts the equation back into regularity.

**This is the theorem card 11 needs, and it is unconditional.**  Instantiating it for the Hankel pair
requires only:

```text
IsHomogIdeal for the secant and chain ideals        both generated by homogeneous elements
IsGradedSubmodule for the standard-monomial span    it is spanned by monomials
the two isCompl statements                          already owned by the corpus
a linear form regular on R/J                        exists_linear_isRegular
the fibre bound                                     exists_generic_fibre_rank + eval_homogenize
```

so what is left on this card is bookkeeping against the corpus's own Hankel definitions, not further
theory.

### Instantiation, first input: homogeneity of the ideals

`HTGeometry/HomogeneousSpan.lean`:

```text
homogeneousComponent_mul_eq_zero_of_lt   multiplying by a homogeneous factor kills low degrees
homogeneousComponent_self_or_zero        a homogeneous polynomial is its own component, or zero
isHomogIdeal_span                        ** an ideal generated by homogeneous elements is
                                            homogeneous **
```

The span induction needs the multiplier decomposed: a general coefficient is the sum of its
homogeneous components, each of which either shifts the degree of the factor or pushes it out of
range, so the component of a product is a combination of components of the factor.

This gives the degeneration theorem's first input for both Hankel ideals — the secant ideal is
generated by the maximal minors, which are homogeneous, and the chain ideal by monomials.  The
remaining inputs are `IsGradedSubmodule` for the standard-monomial span (immediate, since it is a
monomial span) and the fibre bound.

### The Hankel pair satisfies the degeneration hypotheses

`HTGeometry/HankelDegenerationHypotheses.lean`:

```text
support_homogeneousComponent_subset    components shrink the support
isGradedSubmodule_monomialSpan         a span of monomials is graded
isHomogIdeal_of_support                an ideal cut out by a support condition is homogeneous
isHomogIdeal_finiteHankelSecantIdeal   ** the secant ideal is homogeneous **
isHomogIdeal_finiteHankelChainIdeal    ** so is the chain ideal **
isGradedSubmodule_hankelStandardSpan   ** and the standard-monomial span is graded **
```

All three follow from the same observation — taking a homogeneous component only shrinks the support
— together with the support characterisations already proved for these objects, and for the secant
ideal from `homogeneousComponent_mem_finiteHankelSecantIdeal`, which this card's own graded
degeneration module supplies.

So four of the five hypotheses of `forall_mem_of_degeneration` are discharged for this pair: the two
homogeneity conditions, the gradedness of the complement, and (from the corpus)
`isCompl_finiteHankelSecantIdeal_standardSpan` and `isCompl_finiteHankelChainIdeal_standardSpan`.
**The only remaining input is the fibre bound** — that the graded pieces of the family are finitely
generated over `K[t]`, so that `exists_generic_fibre_rank` applies degree by degree, with
`eval_homogenize` identifying the fibre at `t = 1`.

### The graded pieces of the family are modules over the base line

`HTGeometry/FamilyDegreeModule.lean`:

```text
polyMvAlgebra       the base line acts on the family by mapping coefficients
isXHomog_smul       that action preserves the x-degree
xDegreeSubmodule    ** so each x-degree is a module over the base line **
```

Scaling by a polynomial in the extra variable multiplies coefficientwise by constants, which does not
change the `x`-degree.  This is what makes the degeneration a family of *graded pieces* over the base
line rather than merely a family of rings — and it is the setting in which
`exists_generic_fibre_rank` can be applied degree by degree.

(Mathlib has no `Algebra (Polynomial K) (Polynomial A)` instance for a `K`-algebra `A`; the one
declared here is the canonical coefficient map, stated only for the polynomial-ring case so it
cannot collide with the identity algebra on `Polynomial K`.)

What the fibre bound still needs from here: that `xDegreeSubmodule` is finitely generated over the
base line — it is generated by the finitely many monomials of that degree — and the identification of
its two fibres with the degree-`e` parts of `R/(J+l)` and `R/(I+l)`.

### The graded pieces are finite dimensional

`HTGeometry/GradedPieceFinite.lean`:

```text
degreeExponents                            the exponents of a given total degree, as a finset
mem_degreeExponents                        membership is the degree condition
homogeneousSubmodule_eq_span               the degree-e polynomials are spanned by those monomials
finiteDimensional_homogeneousSubmodule_fin ** hence each graded piece is finite dimensional **
```

The finset comes from the tuples of naturals with a given sum, transported along the equivalence
between finitely supported functions and functions on a finite type.

**This discharges the finiteness hypothesis carried by the Hilbert-function criterion and by the
degeneration theorem** — `forall_mem_of_hilbert`, `hilbert_of_forall_mem` and
`forall_mem_of_degeneration` all assume `∀ e, FiniteDimensional K (homogeneousSubmodule σ K e)`, and
over `Fin N` it now holds unconditionally.  (The corpus already had this for `ℂ`; the new statement
is for an arbitrary field.)
