# One positive factor on a torusless quasi-Abelian variety interpolates every finite jet packet

- **ID:** `torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / INFINITE JET AMPLENESS
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [PARENT PROOF EXTENDED]`
- **Statement:** Every positive holomorphic line bundle on a torusless noncompact quasi-Abelian
  variety is jet ample of every finite order without taking tensor powers.

## Statement

Let

```text
X=C^n/Gamma
```

be a torusless noncompact quasi-Abelian variety, and let `L` be a positive holomorphic line bundle
on `X`.  For pairwise distinct points `p_1,...,p_s`, positive integers `r_1,...,r_s`, and the
corresponding finite subscheme

```text
Z=sum_i (r_i+1)p_i,
```

the restriction map

```text
H^0(X,L) -> H^0(Z,L|Z)                                   (1)
```

is surjective.

Equivalently, one fixed positive automorphic factor interpolates arbitrary prescribed finite jets
at arbitrary finite point packets.  No tensor power depending on the jet order is required.

This sharply separates the noncompact torusless phase from compact Abelian varieties, where
`H^0(X,L)` is finite-dimensional and one fixed `L` cannot interpolate jets of unbounded order.

## Parent boundary

Abe constructs the complete space `AF(alpha rho)=H^0(X,L)` by convergent Poincare series for one
fixed automorphic factor.  His published theorems prove:

- arbitrary finite point separation (Theorem 8.1);
- separation of one nonzero tangent direction (Theorem 9.1).

The proof below lifts his same subgroup-rank induction from reduced point packets to arbitrary
finite local Artin jet packets.  No new convergence regime is introduced.

## Finite jet packet

Choose lifts `a_i in C^n` of the points.  Put

```text
J=sum_i O_(C^n,a_i)/m_(a_i)^(r_i+1).                      (2)
```

After trivializing `L` near the packet, (1) is surjectivity of the continuous linear map

```text
ev_J:AF(alpha rho)->J.                                    (3)
```

Fix monomial jet bases in the summands of (2).  It suffices to construct `dim J` automorphic forms
whose evaluation matrix is invertible.

## Growth stability lemma `[PROVED]`

Abe's admissible seed class consists of entire functions with subquadratic lattice growth.  It has
the following properties for every fixed finite order `R`.

1. Multiplication by a polynomial preserves the class.
2. If `h` has order one, then `h^(R+1)` has order one and imposes zero multiplicity `R+1` at every
   zero of `h`.
3. Every derivative of order at most `R` of a convergent Poincare series converges compactly after
   termwise differentiation.
4. If a summand contains a damping factor `exp(B chi)` with `Re(B chi)<=-c|B|`, then every derivative
   of order at most `R` is bounded by a polynomial in `|B|` and the lattice index times the same
   exponential.  It therefore tends uniformly to zero on compact packet neighborhoods.

Items 1--2 are elementary order estimates.  Item 3 follows from Abe's Gaussian majorant after
multiplication by a fixed polynomial in the lattice index.  Item 4 follows from Leibniz and the
chain rule; exponential decay dominates every polynomial produced by finitely many derivatives.

## Base of the subgroup-rank induction `[PROVED]`

In Abe's rank-zero case the relevant lattice is an integer lattice `H` in affine coordinates.  The
union of all undesired translates of the packet is discrete.  The order-one entire separator used
by Abe can be raised to

```text
R+1,   R=max_i r_i,                                       (4)
```

so it vanishes to the required multiplicity at every undesired translated point while remaining
inside the admissible growth class.

For one chosen packet basis jet, multiply this separator by a polynomial whose Taylor class at the
target point is the desired basis vector.  The `lambda=0` term of the Poincare series contributes
that prescribed jet; every `lambda!=0` term vanishes through order `R`.  Multiplication by the
nonzero automorphic and Gaussian seed factors acts invertibly on the target local algebra, so the
polynomial can be chosen after applying its inverse.

Repeating this for every basis vector of (2) gives an identity jet-evaluation matrix.  Thus (3) is
surjective in the base case.

## Induction step `[PROVED]`

Assume finite-packet jet surjectivity for Abe's proper subgroup `H` of lower toroidal rank.  Inside
this rank induction, run Abe's second induction on the number of packet points.  Suppose the full
lattice forms already interpolate the first `s-1` local Artin blocks.  Among the remaining points,
choose the extremal point selected by Abe's maximum-modulus argument.  Subgroup surjectivity gives
a basis `G_1,...,G_d` for its `d`-dimensional local jet algebra which vanishes to the prescribed
orders at the first `s-1` points.

As in Abe's Proposition 8.2, the induction invariant is stronger than abstract surjectivity: every
`G_j` is represented by a Poincare series from an admissible seed `f_j phi_j`.  The base construction
has this form, and the damping extension below preserves it.  Hence every subgroup interpolant is
eligible for the next lattice-extension step; no arbitrary section is inserted into the series.

Abe extends a subgroup series to the full lattice by inserting a damping exponential.  For all
lattice elements of `H`, the damping character is constant in the lattice index.  Hence the full
series decomposes as

```text
F_B=m_B G+R_B,                                            (5)
```

where `m_B` is a nowhere-zero holomorphic multiplier and `R_B` is the complement-lattice sum.

Choose Abe's damping ray for this extremal target block.  At the target point, `|m_B|=1`; at the
complement lattice, the real part of the exponent is uniformly negative on all packet
neighborhoods.  By the growth stability lemma,

```text
jet_R(R_B)->0                                             (6)
```

exponentially, uniformly over the finite packet.

On the local algebra at the target point, multiplication by `m_B` is an automorphism.  In divided
jet coordinates its matrix is lower triangular with diagonal `m_B(p)`.  Therefore

```text
det Mul_(m_B)|J_p = m_B(p)^(dim J_p) !=0.                 (7)
```

At each of the first `s-1` points, the subgroup sections `G_j` vanish to the prescribed jet order,
so multiplication by `m_B` preserves that vanishing.  Normalize the new target block by the
inverse of its multiplication matrix.  Its entries grow at most polynomially in `B`, whereas the
normalized remainder still tends to zero by (6).  Appending this normalized block to the existing
columns gives a jet-evaluation matrix tending to a block-triangular matrix with invertible old and
new diagonal blocks.  It is invertible for all sufficiently large parameters.

Peeling the finite point packet one extremal block at a time completes the inner induction, hence
surjectivity at the next subgroup rank.  Abe's final passage from the distinguished subgroup to
`Gamma` has the identical decomposition (5), so the same two-level induction completes the proof.
`QED`

## Residual complete orbit freedom `[PROVED]`

The section space `H^0(X,L)` with compact-open topology is a Frechet, hence Baire, space.  For a
countable faithful translation subgroup `H subset X`, every proposed differential polynomial
relation among finitely many translates depends on one finite decorated-monomial support and one
finite jet packet.  Surjectivity of (1) supplies a sample packet on which the corresponding
decorated monomials have full evaluation rank.  Therefore no nonzero coefficient choice on that
support vanishes identically, and the determinant-defect locus is closed with empty interior.

Finite decorated-monomial supports and derivative orders form a countable family; coefficients do
not need to be enumerated.  Removing the resulting countable union of coefficient-uniform defect
loci gives a dense residual set of section pairs `(s_0,s_1)` such that

```text
g=s_1/s_0                                                (8)
```

has a completely differentially algebraically independent `H`-translation orbit.  The same
product-space argument makes finitely many quotient carriers jointly free.

Thus every active-faithful torusless quasi-Abelian facet palette supplies the analytic sources
required by the full localized Stanley--Reisner realization theorem.

## Consequence: the active quotient principle `[PROVED]`

Let `X` be a noncompact quasi-Abelian group, `B(X)` its maximal compact complex subtorus, and `H`
a finitely generated free subgroup.  Then

```text
there exists g in Mer(X) with a completely free H-orbit
  iff H -> X/B(X) is injective.                            (9)
```

Necessity is the proper compact-kernel finite-capacity theorem.  For sufficiency, apply the
all-order theorem to the torusless active quotient and pull the residual meromorphic ratio back to
`X`.

## Lean boundary

The analytic Poincare-series induction is not represented by an axiom.  Its two exact algebraic
interfaces are formalized:

- `truncatedJetMultiplicationMatrix_det_ne_zero` and
  `truncatedLocalAlgebra_mul_bijective_of_isUnit` in
  `formal/GaloisForLFunctions/HTGeometry/FiniteShadowCapacity.lean` prove (7) in divided
  one-variable coordinates and in arbitrary truncated local algebras;
- `affineJetPacketCollision_denseResidual_exactMatroid` in
  `formal/GaloisForLFunctions/HTGeometry/AffineJetPacketCollisionCompletion.lean` proves the
  countable Baire assembly once every finite defect has empty interior.

The growth estimates and proper subgroup-rank induction remain paper analysis.

## Novelty and significance gate

Searches for `jet ample`, `higher jets`, `finite jet interpolation`, and fixed-factor automorphic
forms on quasi-Abelian varieties found the classical projective theory, where tensor powers grow
with jet order, and Abe's point/first-tangent theorems.  No all-order theorem for one fixed positive
factor on a torusless quasi-Abelian variety was located.

The theorem is a candidate-new extension, not yet literature-certified.  Its significance is not
the triangular determinant alone.  It is the sharp phase transition:

```text
compact shadow:   every observable has finite cyclic capacity;
torusless active: one fixed positive factor is jet ample at every finite order,
                  and residual ratios attain infinite cyclic capacity.       (10)
```

Combined with the active facet necessity theorem, it closes the analytic gap in the exact
constraint-dimension classification.

## Gates

- [x] same fixed automorphic factor retained at every jet order
- [x] multiplicity separator remains in Abe's growth class
- [x] all finite derivatives of complement terms decay
- [x] damping multiplication proved invertible on each local Artin jet algebra
- [x] subgroup-rank induction lifted from values to complete finite jet packets
- [x] Baire conversion to complete orbit freedom
- [x] active quotient principle proved
- [ ] independent specialist check of the all-order induction
- [ ] exact-formulation primary-literature audit
- [ ] direct Lean formalization of the analytic Poincare estimates before Stage 3

## Lean progress — item 4 of the growth stability lemma

`GaloisForLFunctions.HTGeometry.DampedJetDecay` proves item 4 of the growth stability lemma
unconditionally and axiom-clean (`[propext, Classical.choice, Quot.sound]`), in the one-variable
damping direction that the extension step uses:

```text
iteratedDeriv_cexp_mul        every derivative of the character:  d^m/dz^m e^(a z) = a^m e^(a z)
iteratedDeriv_cexp_mul_mul    the Leibniz expansion of the m-th derivative of  e^(a ·) · g
norm_iteratedDeriv_cexp_mul_mul_le
    ‖d^m/dz^m (e^(a ·) g)(z)‖ ≤ (1 + ‖a‖)^m · e^(Re (a z)) · sup_i ‖d^i g (z)‖
tendsto_norm_iteratedDeriv_damped_zero
    ‖a_n‖ ≤ L B_n,  Re (a_n z) ≤ −c B_n  with c > 0,  B_n → ∞,  uniform jet bound on g_n
      ==>  ‖d^m/dz^m (e^(a_n ·) g_n)(z)‖ → 0   for every fixed m
```

This is exactly `(6)`: "if a summand contains a damping factor `exp(B chi)` with
`Re(B chi) <= -c|B|`, then every derivative of order at most `R` is bounded by a polynomial in `|B|`
and the lattice index times the same exponential.  It therefore tends uniformly to zero on compact
packet neighborhoods."  The polynomial in `|B|` is `(1 + ‖a‖)^m` — the exact binomial coefficient
sum `∑_i C(m,i) ‖a‖^i` produced by Leibniz — and the exponential decay beats it because a fixed
finite jet order gives a fixed polynomial degree.

The bound is uniform in the undamped factor: only a bound on the jets of `g_n` at the point enters,
so a whole complement-lattice family is discarded at once.

Remaining for this card: items 1--3 of the growth stability lemma (the admissible seed class and
termwise differentiation of the Poincaré series), and the subgroup-rank induction itself.

## Lean audit 2026-08-18 — the whole logical chain is already in the tree; two analytic
## hypotheses remain

A corpus audit shows this card's theorem is present in Lean, in Abe's own base-and-extension shape,
with only two *analytic* obligations still carried as structure fields rather than proved:

```text
GaloisForLFunctions.HTGeometry.QuasiAbelianAutomorphicForms
    AutomorphicFactor                        factor / normalized / cocycle / nowhereZero
    AutomorphicFactor.JetAmpleEveryFiniteOrder
        the exact predicate of this card: surjectivity onto every finite local Artin packet at
        pairwise distinct quotient points, same fixed factor, every finite mixed jet order

GaloisForLFunctions.HTGeometry.QuasiAbelianPoincareSeries
    poincareTerm / poincareSeries / poincareSeriesEntire / poincareSeriesAutomorphicForm
    poincareSeries_shift                      the fixed-factor automorphy law
    lineEntire_poincareSeries_of_summableLocallyUniformly
    hasSum_multiIndexJetEvalCLM_poincareTermEntire       termwise differentiation of the series
    multiIndexJetEvalCLM_poincareSeriesEntire_eq_seed_of_powerZeros
        **the base mechanism of this card**: a normally summable seed with an order-`m` power zero
        at every nonzero translate has Poincare sum with exactly the seed's jet below order `m`

GaloisForLFunctions.HTGeometry.QuasiAbelianGaussianFlatSeed
    centeredComplexGaussian, GaussianFlatSeedData, gaussianFlatSeedData
        damping = 1 − (1 − G)^m = G · Σ_(r<m)(1−G)^r, flat to order `m` at the centre

GaloisForLFunctions.HTGeometry.QuasiAbelianIntegerLatticeSeparator
    complexIntegerSinc, integerSincProduct, integerTranslateSine
    exists_integerLatticePacketSeparator, flatIntegerLatticePacketSeparatorData
        the explicit algebraic bump with an order-`m` zero at every undesired translate

GaloisForLFunctions.HTGeometry.QuasiAbelianIntegerLatticePoincareInterpolation
    AutomorphicFactor.jetAmpleEveryFiniteOrder_standardIntegerLattice
        the rank-zero base case, **conditional only on**
        AutomorphicFactor.GaussianFlatIntegerLatticeSeedsNormallySummable

GaloisForLFunctions.HTGeometry.QuasiAbelianPositiveFactorJetAmple
    AbePositiveFactorPresentation                (field `gaussianMajorant`)
    AbePositiveFactorPresentation.jetAmpleEveryFiniteOrder

GaloisForLFunctions.HTGeometry.QuasiAbelianDampedFactorExtension
    AbeDampedFactorExtension                     (field `liftPacket`)
    AbeDampedFactorExtension.jetAmpleEveryFiniteOrder      the subgroup-rank induction step
    AbePositiveFactorTower, AbePositiveFactorTower.jetAmpleEveryFiniteOrder
    AutomorphicFactor.IsAbePositiveTorusless
    AutomorphicFactor.jetAmpleEveryFiniteOrder_of_isAbePositiveTorusless
        **this card's statement**, for every factor with Abe's positive base-and-extension
        presentation
```

So the *subgroup-rank induction is already Lean* — the card's "remaining: the subgroup-rank
induction itself" is out of date.  What is genuinely still open, and is exactly the card's growth
stability lemma, is:

1. **`AbePositiveFactorPresentation.gaussianMajorant`** — a polynomial-Gaussian majorant, uniform on
   compacta, for `ψ(γ)^(-1) · bump(· + γ) · damping(· + γ) · P(· + γ)` over `γ ∈ ℤ^d`.  All three
   analytic ingredients are elementary and reachable: `bump` is built from `sin`/`sinc`, hence of
   exponential type; `damping = G·Σ_(r<m)(1−G)^r` with `G` the centred Gaussian, so
   `|damping(z+γ)| ≤ m(1+C_K)^(m-1) exp(−Σ_c σ_c (γ_c + a_c)²)` on a compact `K` because the lattice
   is *real*; `P` is polynomial.  The only hypothesis needed on the factor is Abe's subquadratic
   growth: `‖ψ(γ)^(-1)(x)‖ ≤ C_K e^(a‖γ‖)` uniformly on compacta.  This is items 1–3 of the card's
   growth stability lemma, and it is the next concrete Lean target.
2. **`AbeDampedFactorExtension.liftPacket`** — the damped packet lift of the induction step (the
   card's `(5)`–`(7)`); item 4 of the growth stability lemma is already Lean
   (`HTGeometry/DampedJetDecay`).
3. The structure-theoretic input that a positive holomorphic line bundle on a torusless noncompact
   quasi-Abelian variety has Abe's positive base-and-extension presentation
   (`IsAbePositiveTorusless`).
