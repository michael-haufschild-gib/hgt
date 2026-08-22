# One positive factor on a torusless quasi-Abelian variety interpolates every finite jet packet

- **ID:** `torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / INFINITE JET AMPLENESS
- **Scientific status:** `[PAPER-PROOF GAP IDENTIFIED] [NOVELTY UNVERIFIED] [PARENT PROOF EXTENDED]`
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

## Formalization audit 2026-08-22 — exact open core

The prior Stage-2 label is not justified.  Abe's primary paper proves finite point separation
(Theorem 8.1) and one tangent-direction separation (Theorem 9.1), but not the all-order packet
theorem stated here.  The proposed lifting argument must additionally construct, at every
subgroup-rank extension and for every enlarged finite jet packet, lower-automorphic seed columns
which simultaneously have the prescribed packet jets, vanish to the prescribed finite orders at
the relevant complement translates, remain locally normally summable after periodization, and have
the normalized polynomial growth required uniformly along Abe's damping ray.

This is not supplied by ordinary finite-jet surjectivity: that predicate provides an interpolant
for each finite packet but no uniform normalized-growth estimate as the enlarged packet grows.
The Lean corpus records the same missing object as the `mult` / `hnormal` / `hmaj` inputs of
`abeDampingPacketDataOfMultiplier` and as the `seed` fields of `AbeDampingPacketData`; neither is
derived from positivity or jet ampleness.  Therefore neither
`AutomorphicFactor.IsAbePositiveTorusless` nor its restricted variant is an unconditional
formalization of this card's public theorem.

**[OPEN CORE]** Construct Abe's invariant damping multipliers (equivalently controlled
lower-automorphic seed families) in his period-matrix coordinates with finite mixed-jet
flatness and the required normal-convergence/majorant estimates.  Once that construction is
dependency-closed on paper, its exact Lean theorem can close the subgroup-rank induction.

The finite algebraic portion is now Lean-proved in
`HTGeometry/QuasiAbelianJetAmpleFiniteVanishing`: lower all-order jet ampleness constructs the
lower-automorphic seed columns with arbitrary prescribed packet jets and zero jets at every point
of an arbitrary finite set of nonzero complement translates.  Its axiom report is exactly
`[propext, Classical.choice, Quot.sound]`.  It discharges the `seed_jet` and finite-vanishing
parts of the extension datum, but deliberately does not claim the missing normalized-growth bound.

### Uniform-damping route falsified; positive survivor

The prior growth-stability claim used a uniform constant `c > 0` with
`Re(B·χ(γ)) ≤ -c|B|` over every nonzero complement term.  Abe's actual argument in §7--§9 of
*Construction of automorphic forms for ample factors of quasi-Abelian varieties* proves only a
strict inequality for each fixed complement term.  Uniformity is false in general: for an
irrational real period `α`, the phases `exp(2π i n α)` approach `1` along nonzero `n`, so
`sup_{n ≠ 0} Re(exp(2π i n α) - 1) = 0`.  No fixed negative gap can exist.

**[FALSIFIED AS A ROUTE]** The advertised polynomial-times-`exp(-δB)` majorant over the whole
complement lattice cannot be the general extension estimate.  Its Lean abstraction
`AbeDampingPacketData.majorant` is stronger than Abe's cited argument and is not discharged by
the card.

**Positive survivor `[PAPER-PROVED]`:** every *finite* nonresonant complement subpacket has a
strict uniform gap, hence all of its fixed finite jets decay exponentially after multiplication by
the damping profile.  `DampedJetDecay` already formalizes the one-variable polynomial-times-
exponential calculation.  This does not control the infinite tail.

**Stronger replacement `[CONJECTURE]`:** replace the false global-gap lemma by a two-scale
normal-family estimate: uniformly control a Gaussian tail independently of the damping parameter,
then prove finite-jet decay on a parameter-dependent finite head with an envelope strong enough to
justify passage to the full Poincaré sum.  The first exact open implication is a summable,
derivative-stable domination theorem in Abe's period-matrix coordinates; it must be proved or
refuted before returning this card to Stage 2.

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

## Growth stability lemma `[PAPER-PROOF GAP]`

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

## Induction step `[PAPER-PROOF GAP]`

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

## Residual complete orbit freedom `[CONDITIONAL ON ALL-ORDER JET AMPLENESS]`

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

## Consequence: the active quotient principle `[CONDITIONAL ON ALL-ORDER JET AMPLENESS]`

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

## Lean status 2026-08-18 (second pass) — the growth stability lemma, items 1 and 2

The audit above identified `AbePositiveFactorPresentation.gaussianMajorant` as the next concrete
target and noted that the separator data is obtained by choice and therefore carries no growth
clause.  Two of the three analytic ingredients are now Lean-certified, and the missing growth clause
has been added to the separator construction itself.

### The correct growth notion is a *strip* bound, not exponential type

The Poincaré series is over the **real** lattice `ℤ^d ⊂ ℂ^d`.  Translating a compact set by a
lattice vector moves only the real parts; the imaginary parts stay inside one fixed polystrip.  So
the right growth clause for the algebraic bump is not "exponential type" but

```text
StripBounded f  :  ∀ V, ∃ C ≥ 0, ∀ x with |Im (x_c)| ≤ V for all c,  ‖f(x)‖ ≤ C,
```

a *uniform* bound along the entire lattice.  Abe's bump satisfies it, because both of its building
blocks do: `|sin(u+iv)| ≤ e^{|v|}` has no real growth at all, and the normalized sinc inherits the
same bound outside the unit disc while being continuous — hence bounded — inside it.  Consequently
the whole decay of the majorant has to come from the Gaussian damping, and it does.

### `HTGeometry/MultivariateEntireStripBound.lean` (new)

- `norm_complexSin_le_exp_abs_im` — the elementary strip bound for `Complex.sin`.  (The same
  estimate is `HTGeometry.norm_csin_le_exp_abs_im` in `WaveTraceSpectrum`, but that module imports
  all of Mathlib and so cannot be a base dependency of the quasi-Abelian chain.)
- `StripBoundedOne`, `StripBounded` — the one-variable and multivariate classes.
- `stripBounded_of_apply_eq_const`, `StripBounded.mul`, `.pow`, `.add`, `.sub`, `.smul`,
  `.finsetProd`, `.finsetSum` — the full closure package.

### `HTGeometry/QuasiAbelianIntegerLatticeSeparator.lean` (extended)

- `stripBoundedOne_sinPi`, `stripBoundedOne_complexIntegerSinc` — the two one-variable bounds.
- `stripBounded_coordinateEntire`, `stripBounded_integerSincProduct`,
  `stripBounded_integerTranslateSine` — transported to the multivariate factors.
- `exists_integerLatticePacketSeparator` now also asserts `StripBounded separator`.
- `exists_flatIntegerLatticePacketSeparator` now also asserts `StripBounded bump`, proved from
  `bump = 1 - (1 - (c⁻¹ • separator)^m)^m` by the closure package.
- `FlatIntegerLatticePacketSeparatorData` carries the new field `bump_stripBounded`, so the
  canonical chosen separator used by the majorant now exposes its growth clause.

This is **item 1** of the card's growth stability lemma (the admissible seed class), and it is
strictly stronger than the card's paper formulation: no exponential factor is needed at all.

### `HTGeometry/QuasiAbelianGaussianLatticeDecay.lean` (new)

- `norm_centeredComplexGaussian_apply` — `‖G(x)‖ = exp(-∑ σ_i (u_i² - v_i²))` with `u, v` the real
  and imaginary parts of `x - centre`.
- `exists_coordinate_bound_of_isCompact` — compact sets have uniformly bounded coordinates.
- `exists_norm_centeredComplexGaussian_lattice_le` — **the decay half**: for every compact `K`
  there is a `C` with

```text
‖G(x + k)‖ ≤ C · exp(-∑_i (σ_i/2) k_i²)      for all x ∈ K and all k ∈ ℤ^d,
```

proved from `(k + t)² ≥ k²/2 - t²` with `t` the compact-uniform real offset.  This is **item 2**
of the growth stability lemma.

All new declarations report `#print axioms … = [propext, Classical.choice, Quot.sound]`.

### What is left for `gaussianMajorant`

1. The polynomial factor: `‖P(x + k)‖ ≤ C_K ∏_i (1 + |k_i|)^{deg P}` — elementary, still to write.
2. The `geom` factor of the damping: bounded along the lattice, since `‖G(x+k)‖` is bounded and
   `geom = ∑_{r<m} (1 - G)^r`.
3. Assembling 1, 2, the strip bound and the Gaussian decay into
   `polynomialGaussianLatticeWeight`, and absorbing the factor's own `ψ(γ)⁻¹` contribution — the
   only remaining factor-dependent input, which is precisely what Abe's *positivity* of the
   presentation supplies (it is a property of the presentation, not an extra assumption).

### `HTGeometry/QuasiAbelianPolynomialLatticeGrowth.lean` (new) — item 3

- `exists_norm_mvPolynomial_eval_le` — coefficientwise:
  `‖eval y P‖ ≤ (∑_{a ∈ supp} |coeff a P|) · ∏_i (1 + ‖y_i‖)^{deg_i P}`, using
  `MvPolynomial.monomial_le_degreeOf` and the exact extension of the monomial product from
  `a.support` to all coordinates (the missing exponents are zero, so it is an *equality*, not an
  inequality).
- `exists_norm_mvPolynomial_lattice_le` — along the lattice: for every compact `K` there is a `C`
  with

```text
‖P(x + k)‖ ≤ C · ∏_i (1 + |k_i|)^{deg_i P}      for all x ∈ K and all k ∈ ℤ^d,
```

from `1 + ‖x_i + k_i‖ ≤ (1 + R)(1 + |k_i|)`.  The exponent vector `A_i = deg_i P` is exactly the
polynomial part of `polynomialGaussianLatticeWeight`.

So items 1, 2 and 3 of the growth stability lemma are Lean-certified.  What remains for
`gaussianMajorant` is the bounded `geom` factor of the damping and the assembly, plus the
factor-side input supplied by Abe's positivity.

### `HTGeometry/QuasiAbelianFlatSeedLatticeBound.lean` (new) — the seed half, unconditional

- `polynomialGaussianLatticeWeight_eq` — the weight splits as
  `(∏_i (1+|k_i|)^{A_i}) · exp(-∑_i σ_i k_i²)`.
- `damping_eq` field added to `GaussianFlatSeedData` (supplied by `rfl` in the constructor), giving
  `damping_apply_eq : damping(z) = 1 - (1 - G(z))^m` pointwise.
- `norm_damping_le` — `‖1-(1-g)^m‖ ≤ ‖g‖ · ∑_{r<m}(1+‖g‖)^r` from the finite geometric identity.
- `exists_norm_damping_lattice_le` — the damping inherits the Gaussian decay:
  `‖damping(x+k)‖ ≤ C · exp(-∑_i (σ_i/2) k_i²)` uniformly on compacta.
- `exists_norm_flatGaussianSeed_lattice_le` — **the seed half of the growth stability lemma, with
  no hypothesis on the automorphic factor**:

```text
‖(bump · damping · P)(x + k)‖ ≤ C · polynomialGaussianLatticeWeight (deg P) (σ/2) k.
```

### `HTGeometry/QuasiAbelianAbePositivityReduction.lean` (new) — the base case is closed

The `gaussianMajorant` field of `AbePositiveFactorPresentation` was an *unverified analytic
assertion*.  It is now **derived** from a single primitive, checkable growth condition:

```lean
def AutomorphicFactor.HasLatticeExponentialGrowth (ψ) : Prop :=
  ∀ K, IsCompact K → ∃ C a, 0 ≤ C ∧ 0 ≤ a ∧ ∀ k x ∈ K,
    ‖(ψ.factor (latticeEquiv k)).1 x)⁻¹‖ ≤ C * exp (a * ∑ i, |k i|)
```

- `exp_mul_sum_natAbs_le` — half of the Gaussian absorbs any exponential:
  `e^{a∑|k_i|}·e^{-∑k_i²/2} ≤ e^{d a²}·e^{-∑k_i²/4}`, from `a t - t²/4 ≤ a²` coordinatewise.
- `gaussianMajorant_of_hasLatticeExponentialGrowth` — the majorant, at `σ = 1`,
  `A_i = deg_i P`, `decay_i = 1/4`.
- `abePositiveFactorPresentationOfGrowth` — the presentation is now *constructible*.
- `AutomorphicFactor.jetAmpleEveryFiniteOrder_of_hasLatticeExponentialGrowth` — **the card's
  statement at the rank-zero base**, for every factor satisfying the growth condition, with
  `#print axioms = [propext, Classical.choice, Quot.sound]`.

### Remaining on this card

1. `AbeDampedFactorExtension.liftPacket` — the damped packet lift of the subgroup-rank induction
   step (item 4 of the growth stability lemma is already Lean, in `HTGeometry/DampedJetDecay`).
2. `AutomorphicFactor.IsAbePositiveTorusless` — Abe's structure theory: that a positive holomorphic
   line bundle on a torusless noncompact quasi-Abelian variety admits the positive
   base-and-extension presentation.  This is the geometric input; the analytic input is now closed.

## Lean status 2026-08-19 (third pass) — the damped extension step is derived from a checkable estimate

Item 1 of "Remaining on this card" (`AbeDampedFactorExtension.liftPacket`) is no longer an
unverified structure field. Four new modules, `lake build`-green, `#print axioms = [propext,
Classical.choice, Quot.sound]`:

```text
HTGeometry/QuasiAbelianCosetPoincareSeries.lean
  complementEmbedding, cosetPoincareSeries
  cosetPoincareSeries_shift          the partial sum over a complement of ΓH in Γ is Γ-automorphic
  cosetPoincareSeriesEntire, cosetPoincareSeriesEntire_mem_forms
  cosetPoincareSeries_eq_seed_add_tail                   the decomposition (5), F = m·G + R
HTGeometry/QuasiAbelianCosetPoincareJet.lean
  hasSum_cosetPoincareTermEntire_of_summableLocallyUniformly
  jet_cosetPoincareSeriesEntire_eq_seed_add_tail         (5) at the level of mixed jets
HTGeometry/QuasiAbelianDampedLiftConstruction.lean
  AbeDampingPacketData, AbeDampingPacketData.toLift
  HasAbeDampingFamily, abeDampedFactorExtensionOfDampingFamily
  jetAmpleEveryFiniteOrder_of_hasAbeDampingFamily
  isAbePositiveTorusless_of_hasAbeDampingFamily
HTGeometry/QuasiAbelianDampingFamilyNonvacuous.lean
  summableLocallyUniformlyOn_of_fintype
  hasAbeDampingFamily_self, abeDampedFactorExtensionSelf                  the interface is inhabited
```

Two structural points.

1. **Why the partial sum, not the full one.** Summing a `ΓH`-automorphic form over all of `Γ`
   repeats each value once per element of `ΓH`. Abe sums over a complement. The resulting series is
   still `Γ`-automorphic, and the reason is formal rather than analytic: writing `δ = η + comp w`,
   the cocycle converts the shifted argument into a shifted index, the seed's own `ΓH`-law absorbs
   `η`, and `w` translates the summation index. Only `upper.factor|_{ΓH} = lower.factor` is used.

2. **What is left is exactly one estimate.** `HasAbeDampingFamily c lower upper` asks for a
   `B`-family of lower seeds with the packet jets of the prescribed lower column and an
   exponentially damped complement remainder. Everything downstream — that the partial sum is an
   upper form, that its jets split as seed plus remainder, that the extension step preserves
   all-order jet ampleness and Abe positivity — is now proved. Concretely the missing object is a
   `ΓH`-invariant multiplier family `m_B` which is the identity on the finite jet packet and whose
   complement translates carry `C·B^r e^{-δB}` times a polynomial-Gaussian lattice weight; that is
   Abe's Proposition 8.2, and it is the sole analytic obligation left on this card.

## Lean status 2026-08-21 — the damping obligation, re-scoped

Two things were established about the remaining item, `HasAbeDampingFamily`.

**1. The multiplier route cannot work.**  A seed of the form `m_B · G` lies in `lower.forms` only if
`m_B` is `ΓH`-invariant, i.e. a holomorphic function on `ℂ^d/ΓH`.  When that quotient is a toroidal
group every such function is constant; otherwise the nonconstant ones are the characters
`exp(λ(x))` with `λ(ΓH) ⊆ 2πiℤ`, whose modulus `exp(B·Re λ(x))` is **linear** in the complement
index and therefore *positive* on half of the complement lattice.  The automorphy factor supplies
only a Gaussian `exp(−σ|z|²)`, so for a fixed `z` with `Re λ(comp z) > 0` the term grows like
`e^{cB}` while the required bound decays like `e^{−δB}`.  No character damps a full complement
lattice.

**2. What the interface actually asks for is vanishing, not damping.**
`GaloisForLFunctions.HTGeometry.QuasiAbelianVanishingDampingFamily` (wired, built, axiom-clean):

```text
abeDampingMajorant_of_jet_vanishing   the majorant field holds with `C = 0` as soon as the packet
                                      jets of the complement Poincaré terms vanish — the bound is
                                      then `0 ≤ 0`, with no `B` dependence
AbeDampingPacketData.ofVanishing      hence the whole packet datum is constructible from a family
                                      of lower-automorphic seeds with the prescribed packet jets
                                      whose complement translates have vanishing packet jets
```

So the analytic obligation of this card is now, exactly: *construct lower-automorphic forms with
the prescribed jets at the finite packet whose translates by the nonzero complement lattice have
vanishing jets there, with the Poincaré series still locally uniformly summable.*  A finite version
— vanishing only for `0 < |z| ≤ Z(B)` with `Z(B) ≍ √(δB/σ)`, the Gaussian tail supplying `e^{−δB}`
beyond, and the interpolant's majorant constant growing at most polynomially in `B` — is the
induction hypothesis of the card (jet ampleness of the lower factor at a finite packet) plus a
growth bound, and is the natural next target.

## Lean status 2026-08-21 (second entry) — the finite version, and why the factor cannot interfere

Two modules, wired, `lake build`-green, axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

### `HTGeometry/MultivariateEntireJetVanishingProduct.lean` — the factor cannot resurrect a jet

```text
partialDerivEntire_mul                Leibniz for a coordinate derivative of entire sources
partialDerivEntire_translate          a coordinate derivative commutes with translation
orderedPartialJetEvalCLM_translate    jets of a translate are jets at the translated point
AllJetsVanish n p f                   every ordered mixed jet up to order n vanishes at p
AllJetsVanish.mono / .value / .partialDeriv
AllJetsVanish.mul_left, .mul_right    **vanishing jets survive multiplication**
AllJetsVanish.translate
allJetsVanish_poincareTermEntire      **a Poincaré summand inherits the vanishing of its seed at
                                       the translated point**
AllJetsVanish.multiIndexJet
multiIndexJetEvalCLM_poincareTermEntire_eq_zero
```

The induction is the Leibniz rule read backwards: each coordinate derivative of `h · f` splits into
`(∂h)·f + h·(∂f)`, and both summands again pair an arbitrary entire factor with something vanishing
to one order less.  Applied to `poincareTermEntire ψ G γ = ψ(γ,·)⁻¹ · G(· + γ)` — the two factors are
`automorphicFactorInverseEntire` and `multivariateEntireTranslate` — it says the automorphy factor
cannot create a packet jet the seed does not have.  So `hvanish` of the damping interface is
*exactly* a condition on the seed's own jets at the translated packet points, which is what jet
ampleness of the lower factor can prescribe.

### `HTGeometry/QuasiAbelianFiniteVanishingDamping.lean` — the finite version

```text
polynomialGaussianLatticeWeight_zero_exponent
abeDampingMajorant_of_finite_vanishing
AbeDampingPacketData.ofFiniteVanishing
```

Vanishing is now required only on a disc: for `0 < ∑ z_k² ≤ Z B`.  Outside it the seed's own
Gaussian decay `exp(−σ₀ ∑ z_k²)` is split as `exp(−(σ₀−σ₁)∑ z_k²)·exp(−σ₁ ∑ z_k²)`; the first
factor is at most `exp(−δB)` as soon as `δ·B ≤ (σ₀−σ₁)·Z B` — that is, radius `≍ √(δB/σ)`, exactly
the scale the previous entry named — and the second is the majorant's own Gaussian lattice weight.
The seed's bound is allowed to grow polynomially in `B` (`C₀·B^r`), as the induction hypothesis
supplies.

### What is left

The card's analytic obligation is now a *finite* interpolation statement with no damping and no
infinite vanishing condition:

> for each `B`, produce a lower-automorphic form with the prescribed jets at the packet `{w i}` and
> vanishing jets at the finitely many translated points `{w i + comp z : 0 < ∑ z_k² ≤ Z B}`, with a
> bound `C₀ B^r · exp(−σ₀ ∑ z_k²)` on its complement Poincaré jets and locally uniform summability.

That is jet ampleness of the *lower* factor at the enlarged finite packet — the induction hypothesis
of the card — together with a growth estimate.  The remaining structural input is that the enlarged
packet is a legitimate packet: the points `w i + comp z` must be pairwise distinct modulo `ΓH`,
which is `PairwiseDistinctModulo` for the enlarged family.

## Lean status 2026-08-21 (third entry) — finite interpolation with vanishing, solved

`GaloisForLFunctions.HTGeometry.EnlargedPacketInterpolant` (wired, built, axiom-clean)

```text
exists_mvPolynomial_packet_and_vanishing
    **one multivariable polynomial with prescribed jets at the packet and vanishing jets at the
    translates**
```

Prescribing jets at the packet *and* zero jets at finitely many translates is a single
interpolation problem on the enlarged packet, so the corpus's own packet surjectivity
(`exists_mvPolynomial_multiIndexJetEvalCLM_eq_arbitrary`) solves it outright — one polynomial
realises every mixed partial below the prescribed order at finitely many distinct points.  The
points are distinct by the previous entry's `pairwiseDistinctModulo_enlargedPacketPoints`, used here
through plain injectivity.

So the *interpolation* half of the card's remaining analytic obligation is closed, and closed
constructively: the interpolant is a polynomial, whose growth is polynomial in the degree.

What the obligation still asks for is that the interpolant be **lower-automorphic**, which a
polynomial is not.  The card's own route supplies that from jet ampleness of the lower factor at the
enlarged packet — the induction hypothesis — and what this entry settles is that the enlarged
packet is a legitimate interpolation problem with a solution, so the induction hypothesis has
something to be applied to.  The residue is therefore exactly the growth estimate: the
lower-automorphic interpolant's complement Poincaré jets must be bounded by
`C₀·B^r·exp(−σ₀ ∑ z_k²)`, which combined with `AbeDampingPacketData.ofFiniteVanishing` closes the
damping datum.

## Lean status 2026-08-21 (fourth entry) — the growth estimate, reduced to two sup bounds

`GaloisForLFunctions.HTGeometry.PoincareTermJetGrowth` (wired, built, axiom-clean)

```text
norm_poincareTermEntire_le
    the sup bound for a Poincaré term from the two factors
norm_multiIndexJetEvalCLM_poincareTermEntire_le
    **Cauchy's estimate for a packet jet of a Poincaré term** — the jet at `p` of total degree `n`
    is bounded by `Mψ·Ms/ρⁿ`, where the two sups are taken over the ball of radius `n·ρ` about `p`
norm_multiIndexJetEvalCLM_poincareTermEntire_le_gaussian
    **the damping bound itself**: a Gaussian bound `Cψ·exp(−σ₀·S)` on the inverse automorphy factor
    and a polynomial bound `Cs·B^r` on the seed give
    `‖jet‖ ≤ (Cψ·Cs/ρⁿ)·B^r·exp(−σ₀·S)`
```

This is exactly the hypothesis `hbound` of `abeDampingMajorant_of_finite_vanishing`, so the card's
remaining analytic obligation is now split into two *sup* bounds on one fixed polydisc, with no
derivatives left in either:

1. `‖ψ(γ_z, y)⁻¹‖ ≤ Cψ · exp(−σ₀ ∑ z_k²)` for `y` in a ball about the packet point — this is the
   Riemann-form positivity of the lattice, i.e. `IsAbePositiveTorusless`;
2. `‖seed(y + γ_z)‖ ≤ Cs · B^r` on the same ball — the induction hypothesis's own growth bound on
   the lower-automorphic interpolant.

No estimate on jets of the seed is needed: Cauchy's inequality converts a sup bound into every
mixed partial, and the Leibniz layer of the second entry converts vanishing jets in the same way.
So the card's residue is now a *pointwise* statement about the automorphy factor and a *pointwise*
statement about the interpolant, both on a compact set.

## Lean status 2026-08-21 (fifth entry) — the positive factor, and its Gaussian decay

> **CORRECTED (fifteenth entry).**  Read with the correction below: until the `IsSemicharacterOn`
> repair the semicharacter law in these statements was quantified over all of `ℂ^d`, which forces
> `H = 0`.  The results held only for the trivial factor.

The first of the two pointwise inputs named in the fourth entry is now Lean, unconditionally.

`GaloisForLFunctions.HTGeometry.AppellHumbertGaussianBound` (wired, built, axiom-clean)

```text
IsHermitianForm.self_eq_re, star_self, smul_right, re_smul_add
IsHermitianForm.norm_sq_le    **Cauchy--Schwarz for a positive semidefinite Hermitian form**
IsHermitianForm.norm_le_sqrt  its square-root form
norm_inv_appellHumbertFactor_le
    **the Gaussian bound**: for `(H z z).re ≤ C²`,
    `‖e(γ, z)⁻¹‖ ≤ exp(π C²)·exp(−(π/4)·(H γ γ).re)`
```

The mechanism is that half of the quadratic exponent pays for the cross term and half survives:
`‖e(γ,z)⁻¹‖ = exp(−π·Re H(z,γ) − (π/2)·H(γ,γ))`, Cauchy--Schwarz gives
`−Re H(z,γ) ≤ C·√(H(γ,γ))`, and `π C u − (π/2) u² ≤ π C² − (π/4) u²` because the difference is
`π (C − u/2)²`.  Cauchy--Schwarz itself is proved from scratch for this Hermitian form — the
positivity `0 ≤ Re H(x + λ y, x + λ y)` at `λ = −s·H(x,y)` gives
`0 ≤ a − 2s‖w‖² + s²‖w‖² b` for every real `s`, and the two cases `b = 0`, `b > 0` are settled by
`s = (a+1)/(2‖w‖²)` and `s = 1/b`.

`GaloisForLFunctions.HTGeometry.AppellHumbertAutomorphicFactor` (wired, built, axiom-clean)

```text
IsHermitianForm.zero_left, zero_right, hermLeft
semicharacter_zero                     a unit-modulus semicharacter is `1` at zero
continuous_appellHumbertFactor         continuity, from finite dimensionality
lineEntire_appellHumbertFactor         **entireness on every line**: the exponent is affine there
appellHumbertAutomorphicFactor         **the Appell--Humbert factor is an `AutomorphicFactor` for
                                       every period group**
norm_inv_appellHumbertAutomorphicFactor_le
                                       **the Gaussian bound in the form the damping estimate
                                       consumes**
```

So the card's positivity input is no longer an interface: a positive semidefinite Hermitian form
and a unit-modulus semicharacter *produce* an automorphic factor whose inverse decays like
`exp(−(π/4)·H(γ,γ))` uniformly on any set where the base point has bounded form-size.  Composed with
`norm_multiIndexJetEvalCLM_poincareTermEntire_le_gaussian` of the fourth entry, the damping
hypothesis `hbound` now needs only the seed's own sup bound `‖seed(y + γ)‖ ≤ Cs·B^r`.

## Lean status 2026-08-21 (sixth entry) — the damping hypothesis, closed against a fixed ball

> **CORRECTED (fifteenth entry).**  Read with the correction below: until the `IsSemicharacterOn`
> repair the semicharacter law in these statements was quantified over all of `ℂ^d`, which forces
> `H = 0`.  The results held only for the trivial factor.

`GaloisForLFunctions.HTGeometry.PoincareTermAppellHumbertDecay` (wired, built, axiom-clean)

```text
IsHermitianForm.sub
norm_poincareTerm_appellHumbert_le
    **the Poincaré term of a lower-automorphic seed decays like the difference form**:
    `‖ψ(γ,z)⁻¹·seed(z+γ)‖ ≤ exp(π C²)·exp(−(π/4)·(H_u − H_l)(γ,γ))·‖seed(z)‖`
norm_multiIndexJetEvalCLM_poincareTerm_appellHumbert_le
    **its packet-jet form**:
    `‖jet‖ ≤ (exp(π C²)·M_s/ρⁿ)·exp(−(π/4)·(H_u − H_l)(γ,γ))`
```

The structural point is that for a *lower-automorphic* seed the lattice dependence collapses.
`seed(z + γ) = e_l(γ, z)·seed(z)`, so

```text
poincareTerm ψ_u seed γ z = (e_u(γ,z)⁻¹ · e_l(γ,z)) · seed z,
```

and the bracket is the Appell--Humbert expression of the **difference form** `D = H_u − H_l` with
the quotient semicharacter — whose modulus does not depend on the semicharacter at all.  So Abe
positivity in the exact form `D ⪰ 0` gives the Gaussian factor, and the seed enters **only through
its size at the base point**.

Consequence for the card.  The damping hypothesis `hbound` of
`abeDampingMajorant_of_finite_vanishing` no longer needs any control of the seed over the lattice:
it needs `‖seed‖ ≤ M_s` on one fixed ball around the packet point, with `M_s = C_s·B^r` supplied by
the induction hypothesis, and `D ⪰ 0` with `(D y y).re ≤ C²` on the same ball.  Both are compact
statements about a single ball, and the whole `exp(−σ₀ ∑ z_k²)` decay is now proved rather than
assumed, with `σ₀ = π/4` measured in the difference form.

## Lean status 2026-08-21 (seventh entry) — Abe positivity in coordinates, and the majorant

> **CORRECTED (fifteenth entry).**  Read with the correction below: until the `IsSemicharacterOn`
> repair the semicharacter law in these statements was quantified over all of `ℂ^d`, which forces
> `H = 0`.  The results held only for the trivial factor.

`GaloisForLFunctions.HTGeometry.AbePositiveGaussianMajorant` (wired, built, axiom-clean)

```text
hermitian_sum_left, hermitian_sum_right    the bilinear expansion of a Hermitian form on sums
abeGram D v                                the real Gram matrix `Re D(v_i, v_j)` of the difference
                                           form on a complement basis
re_hermitian_latticeSum
    **the form at a lattice point is the real quadratic form of the Gram matrix**:
    `Re D(∑ z_i v_i, ∑ z_i v_i) = z ⬝ (abeGram D v) *ᵥ z`
exists_gaussian_of_posDef
    **positive definiteness of that Gram matrix turns the Gaussian in the form value into a
    Gaussian in the lattice coordinates**: `exp(−t·D(γ,γ)) ≤ exp(−σ ∑ z_i²)` with `σ = t·μ > 0`
norm_multiIndexJetEvalCLM_le_gaussianLatticeWeight
    **the damping majorant**: `‖jet‖ ≤ (exp(π C₀²)·M_s/ρⁿ) · polynomialGaussianLatticeWeight`
```

The coercivity step is the corpus's own `posDef_coercive`, so the only new input is the bilinear
identification of the form on the lattice with a real quadratic form.

**This closes the `majorant` field of `AbeDampingPacketData` for Appell--Humbert data.**  Its
hypotheses are, in full:

* upper and lower factors both of Appell--Humbert type, for Hermitian forms `H_u`, `H_l` and
  unit-modulus semicharacters — and the factors are *constructed*, not assumed
  (`appellHumbertAutomorphicFactor`);
* the seed transforms by the lower factor — which is `seed_mem` of the damping datum itself;
* **Abe positivity**, in the exact coordinate form `Matrix.PosDef (abeGram (H_u − H_l) v)` for the
  complement basis `v`, plus `(H_u − H_l) ⪰ 0` on the whole space;
* the seed's size `M_s` and the difference form's size `C₀²`, both on a **single fixed ball** around
  the packet point.

So `IsAbePositiveTorusless` is no longer an interface at this level: it is the positive-definiteness
of one explicit `c × c` real matrix.  What the card still needs to assemble a full
`AbeDampingPacketData` is the remaining fields — `normal` (locally uniform summability of the
complement Poincaré series, for which the majorant is the standard input), `seed`/`seed_jet` (the
induction hypothesis together with `EnlargedPacketInterpolant`), and the bookkeeping fields
`compat`, `decomp`.

## Lean status 2026-08-21 (eighth entry) — the `normal` field, closed

> **CORRECTED (fifteenth entry).**  Read with the correction below: until the `IsSemicharacterOn`
> repair the semicharacter law in these statements was quantified over all of `ℂ^d`, which forces
> `H = 0`.  The results held only for the trivial factor.

`GaloisForLFunctions.HTGeometry.AbePoincareLocalNormal` (wired, built, axiom-clean)

```text
hermitian_self_eq_sum        a Hermitian form on `ℂ^d` expands in the standard basis
continuous_hermitian_self_re **hence `y ↦ Re D(y,y)` is continuous**
summableLocallyUniformlyOn_poincareTerm_appellHumbert
    **the complement Poincaré series of a lower-automorphic seed converges locally normally**
```

This is the `normal` field of `AbeDampingPacketData`, proved rather than assumed.  The mechanism is
the Weierstrass M-test through the corpus's own
`summableLocallyUniformlyOn_of_polynomialGaussianLattice_bound`: on a compact set the difference
form and the seed are bounded — both bounds are *free*, the first by the standard-basis expansion
and the second because the seed is continuous — and the lattice dependence is the Gaussian weight
of the previous entry, which is summable.

Status of the damping datum for Appell--Humbert data.  Of the fields of `AbeDampingPacketData`:

* `majorant` — **proved** (seventh entry), from `Matrix.PosDef (abeGram (H_u − H_l) v)`;
* `normal` — **proved** (this entry), from the same positivity;
* `le`, `compat`, `comp`, `comp_mem`, `decomp` — bookkeeping about the two period groups and the
  complement embedding, fixed by the choice of `H_l` agreeing with `H_u` along `ΓH`;
* `seed`, `seed_mem`, `seed_jet` — the induction hypothesis (jet ampleness of the lower factor),
  together with `EnlargedPacketInterpolant` for the finite interpolation with vanishing.

So the two analytic fields are closed, and what remains is the group bookkeeping and the induction's
own supply of seeds.

## Lean status 2026-08-21 (ninth entry) — `hbound` in the exact shape the majorant consumes

> **CORRECTED (fifteenth entry).**  Read with the correction below: until the `IsSemicharacterOn`
> repair the semicharacter law in these statements was quantified over all of `ℂ^d`, which forces
> `H = 0`.  The results held only for the trivial factor.

`GaloisForLFunctions.HTGeometry.AbeDampingBoundBridge` (wired, built, axiom-clean)

```text
abeDampingBound_of_appellHumbert
    **the hypothesis `hbound` of `abeDampingMajorant_of_finite_vanishing`**, for Appell--Humbert
    data: `‖jet‖ ≤ C₀·B^r·exp(−σ₀ ∑ z_k²)` with a single `σ₀ > 0` and a single `C₀ ≥ 0`, uniform in
    the packet index, the seed index, the lattice point and `B`
```

Its inputs are exactly three, and no analytic estimate is among them:

1. the two factors are Appell--Humbert, and the seed family transforms by the lower one;
2. Abe positivity, as `Matrix.PosDef (abeGram (H_u − H_l) v)` on the complement basis;
3. two sup bounds on one ball of radius `Rad` around each packet point — `(H_u − H_l)(y,y) ≤ C₀²`,
   which is a property of the forms alone, and `‖seed B j‖ ≤ C_s·B^r`, which is the induction
   hypothesis's own growth bound.

The Cauchy estimate is taken at **unit radius**, which is what makes the constant independent of the
jet order: the radius of the ball is the jet order itself, and the hypothesis `hrad` only asks that
the finitely many jet orders of the packet fit inside `Rad`.

Chain status for the card's analytic obligation.  `abeDampingBound_of_appellHumbert` feeds
`abeDampingMajorant_of_finite_vanishing` (which adds the `exp(−δB)` from vanishing on a disc, and is
already in the tree), and that produces the `majorant` field; `normal` is the eighth entry.  So both
analytic fields of `AbeDampingPacketData` are proved from positivity and the induction hypothesis's
growth bound, with no remaining estimate.

`AbeDampingBoundBridge` also gained `appellHumbertAutomorphicFactor_compat`, the `compat` field: the
upper factor restricts to the lower one along `ΓH` exactly when the two Hermitian forms and the two
semicharacters agree there.  Of `AbeDampingPacketData`'s ten fields, the ones still not supplied by
a theorem are the pure lattice data (`le`, `comp`, `comp_mem`, `decomp`) and the seeds
(`seed`, `seed_mem`, `seed_jet`), which are the induction hypothesis itself.

## Lean status 2026-08-21 (tenth entry) — CORRECTION to entries six, seven, eight, nine

The sixth entry claimed that "for a lower-automorphic seed the lattice dependence collapses",
using the transformation law `seed(x + γ) = e_l(γ,x)·seed(x)` for `γ ∈ Γ`.  **That hypothesis is
unsatisfiable in the intended application.**  The seed is automorphic only for the *smaller* group
`ΓH`; the complement translates `comp z` are precisely the elements of `Γ` that are *not* in `ΓH`,
so `seed(x + comp z)` is a genuinely new value.  A seed satisfying the law for all of `Γ` would make
the complement Poincaré series degenerate.  The theorems as stated were true implications, but with
a hypothesis no seed of the induction can meet.

The four modules are corrected.  The right invariant is the **normalised modulus**
`|θ(y)|·exp(−(π/2)·Re H_l(y,y))`, which is `ΓH`-periodic (`thetaNorm_add`, already in the tree), so
the honest hypothesis is that it is bounded:

```text
‖seed y‖ ≤ M · exp((π/2) · Re H_l(y,y))     for every y
```

With it the computation goes through unchanged, and for the same reason: expanding
`Re H_l(x+γ, x+γ) = Re H_l(x,x) + 2·Re H_l(x,γ) + H_l(γ,γ)` cancels the lower form against the upper
one, leaving the exponent

```text
(π/2)·Re H_l(x,x)  −  π·Re D(x,γ)  −  (π/2)·D(γ,γ),      D = H_u − H_l,
```

whose second and third terms are exactly the exponent of the inverse Appell--Humbert factor of `D`.
So `norm_inv_appellHumbertFactor_le` applies verbatim and the Gaussian decay is the same.  The only
change downstream is that the seed's contribution is the global constant `M` together with a bound
on `Re H_l` over the ball — the latter free by `continuous_hermitian_self_re`.

Corrected statements (all wired, built, axiom-clean):

```text
IsHermitianForm.re_add_self                       the expansion of the square
norm_poincareTerm_appellHumbert_le                 hypothesis is now `hseednorm`
norm_multiIndexJetEvalCLM_poincareTerm_appellHumbert_le
                                                   hypotheses `hzsup` and `hLsup` on one ball
norm_multiIndexJetEvalCLM_le_gaussianLatticeWeight the majorant, same shape
summableLocallyUniformlyOn_poincareTerm_appellHumbert
                                                   the `normal` field, same conclusion
abeDampingBound_of_appellHumbert                   `hbound`, with `M = C_s·B^r`
```

Effect on the card.  The conclusions of entries seven to nine are unchanged; what changed is the
hypothesis that the induction must supply.  It is now: **the lower-automorphic interpolant has
normalised modulus at most `C_s·B^r`** — a statement about the seed alone, with no reference to the
complement lattice, and exactly the quantity Abe's argument controls.

## Lean status 2026-08-21 (eleventh entry) — the damping datum is constructible

> **CORRECTED (fifteenth entry).**  Read with the correction below: until the `IsSemicharacterOn`
> repair the semicharacter law in these statements was quantified over all of `ℂ^d`, which forces
> `H = 0`.  The results held only for the trivial factor.

`GaloisForLFunctions.HTGeometry.AbeDampingPacketConstruction` (wired, built, axiom-clean)

```text
abeDampingPacketDataAppellHumbert
    **every field of `AbeDampingPacketData`, for a pair of Appell--Humbert factors**
```

`normal` and `majorant` are the theorems of the eighth and ninth entries; `compat` is the
Appell--Humbert compatibility; the remaining fields are the induction step's own data:

* the two period groups and their complement — `le`, `comp`, `comp_mem`, `decomp`;
* the seed family — with prescribed jets (`seed_jet`), lower-automorphic (`seed_mem`), of bounded
  normalised modulus `C_s·B^r` (`hseednorm`), and vanishing at the complement translates inside a
  disc of squared radius at least `κ·B` (`hvanish`).

The `exp(−δB)` of the majorant is produced with `δ = (σ₀/2)·κ`, so the vanishing radius `√(κB)` and
the Gaussian rate `σ₀` of Abe positivity determine the damping rate outright.

Consequently `HasAbeDampingFamily` is now precisely the statement that the induction hypothesis
supplies such a seed family for every finite jet packet, and
`jetAmpleEveryFiniteOrder_of_hasAbeDampingFamily`, already in the tree, closes the induction step.

## Lean status 2026-08-21 (twelfth entry) — the corpus's own majorant hypothesis, discharged

> **CORRECTED (fifteenth entry).**  Read with the correction below: until the `IsSemicharacterOn`
> repair the semicharacter law in these statements was quantified over all of `ℂ^d`, which forces
> `H = 0`.  The results held only for the trivial factor.

The tree already contained a reduction of the polynomial-Gaussian Poincaré majorant to a single
primitive condition on the factor,
`QuasiAbelianAbePositivityReduction.gaussianMajorant_of_hasLatticeExponentialGrowth`, whose
hypothesis is

```text
AutomorphicFactor.HasLatticeExponentialGrowth ψ :
  ∀ K compact, ∃ C a ≥ 0, ∀ k x ∈ K, ‖ψ(γ_k)(x)⁻¹‖ ≤ C · exp(a · ∑ |k_i|)
```

`GaloisForLFunctions.HTGeometry.AppellHumbertLatticeGrowth` (wired, built, axiom-clean) discharges
it for the Appell--Humbert class:

```text
hasLatticeExponentialGrowth_appellHumbert
    **the Appell--Humbert factor of a positive semidefinite Hermitian form satisfies it, with
    growth rate `a = 0`**
```

The reciprocal factor is not merely subexponential in the lattice index — it is *bounded*: the
exponent `−π·Re H(x,γ) − (π/2)·H(γ,γ)` is at most `π·C²` uniformly once `Re H(x,x) ≤ C²` on the
compact set, and the second term is `≤ 0` by positive semidefiniteness.  The compact bound on
`Re H(x,x)` is free by `continuous_hermitian_self_re`.

So the majorant hypothesis of the corpus's own chain, previously an unverified analytic field of
`AbePositiveFactorPresentation`, is now a theorem for every Appell--Humbert factor of a positive
form — which is exactly the class the card's `L` positive produces.

## Lean status 2026-08-21 (thirteenth entry) — polynomially bounded seeds

> **CORRECTED (fifteenth entry).**  Read with the correction below: until the `IsSemicharacterOn`
> repair the semicharacter law in these statements was quantified over all of `ℂ^d`, which forces
> `H = 0`.  The results held only for the trivial factor.

The seeds the induction actually produces are a lower-automorphic form of bounded normalised
modulus multiplied by an **interpolating polynomial** (`EnlargedPacketInterpolant`), so their
normalised modulus is bounded only polynomially.  The previous entries required it to be bounded,
which a polynomial multiple never is.  Two changes close that gap.

First, `PoincareTermAppellHumbertDecay` was refactored so that the normalised-modulus bound is
needed **only at the translated point**:

```text
norm_poincareTerm_appellHumbert_le_at    the hypothesis is `‖seed (z+γ)‖ ≤ M·exp((π/2)Re H_l(z+γ,z+γ))`
norm_poincareTerm_appellHumbert_le       the earlier global-hypothesis form, now a corollary
```

The proof never used more than that; making it explicit is what lets the constant depend on `γ`.

Second, `GaloisForLFunctions.HTGeometry.PoincareTermPolynomialSeed` (wired, built, axiom-clean):

```text
one_add_pow_le_exp        `(1 + t)^N ≤ exp(N·t)`, from `1 + t ≤ exp t`
poly_gaussian_absorb      **a Gaussian in the lattice index absorbs any power of the index**:
                          `(1+t)^N · exp(−σ s) ≤ exp((N·Cv)²/(2σ)) · exp(−(σ/2) s)` when `t ≤ Cv√s`
norm_poincareTerm_appellHumbert_poly_le
                          the decay estimate for `‖seed y‖ ≤ M·(1+‖y‖)^N·exp((π/2)Re H_l(y,y))`
```

The absorption is algebraic, not asymptotic: it is the maximum of `a·u − (σ/2)u²`, which
`(σu − a)² ≥ 0` gives outright.  Half the Gaussian rate pays for any power of the lattice index, so
the polynomial factor of the interpolant costs a constant and nothing else.

Effect on the card.  The seed hypothesis of the damping datum is now exactly Abe's own admissible
class — the card's "subquadratic lattice growth" — rather than a strengthening of it that the
induction could not deliver.

## Lean status 2026-08-21 (fourteenth entry) — the seed hypothesis is a local condition

> **CORRECTED (fifteenth entry).**  Read with the correction below: until the `IsSemicharacterOn`
> repair the semicharacter law in these statements was quantified over all of `ℂ^d`, which forces
> `H = 0`.  The results held only for the trivial factor.

`GaloisForLFunctions.HTGeometry.AppellHumbertNormalisedModulus` (wired, built, axiom-clean)

```text
thetaNorm_add_of                     **invariance of the normalised modulus under one period**,
                                     from the transformation law at that period alone
thetaNorm_invariant_of_mem_forms     hence invariance under the whole period group of the factor
norm_le_of_thetaNorm_le              the bound in the shape the decay estimate consumes
thetaNorm_le_of_orbitReaching        **a bound on any set meeting every period orbit is a bound
norm_le_of_orbitReaching             everywhere**
```

The tree's `thetaNorm_add` assumes the transformation law for *every* vector of the ambient space,
which a seed of the induction never has — it is automorphic only for its own period group.  The
pointwise version above needs the law at the one period being translated by, which is exactly what
membership in `lower.forms` supplies.

Effect on the card.  The seed hypothesis of the damping datum —
`‖seed y‖ ≤ M·exp((π/2)·Re H_l(y,y))`, or its polynomial version — is now a **local** condition: it
suffices to bound the normalised modulus on any set `S` with `∀ y, ∃ γ ∈ ΓH, y − γ ∈ S`.  For a
period group of rank `k` in `ℂ^d` such an `S` can be taken to be a slab, so the condition is
checkable where Abe checks it, and no global estimate over the lattice is required.

## Lean status 2026-08-21 (fifteenth entry) — CORRECTION: the semicharacter law was vacuous

Entries five to fourteen stated their results for "Appell--Humbert data".  They did not.  Every one
of them took the semicharacter law in the form

```text
∀ γ γ' : ℂ^d,  χ (γ + γ') = χ γ · χ γ' · exp(−πi · Im H(γ, γ'))
```

quantified over the **whole space**.  That hypothesis has only the trivial model.  The left-hand
ratio `χ(γ+γ')/(χγ·χγ')` is symmetric in `γ, γ'` while `Im H` is antisymmetric, so
`exp(−2πi·Im H(γ,γ')) = 1`, i.e. `Im H(γ,γ') ∈ ℤ` for *every* pair of complex vectors; `Im H` is
ℝ-bilinear and continuous, so `Im H ≡ 0`; and a Hermitian form with vanishing imaginary part is
zero.  So the whole chain was a correct statement about the trivial factor `H = 0` and nothing else.

Worse for the entries that invoked positivity: with `H_u = H_l = 0` the difference form is zero, its
Gram matrix is the zero matrix, and `Matrix.PosDef` of it is false.  Those entries described
hypotheses with no joint model at all.

**The repair.**  A semicharacter is a statement about the lattice, not the ambient space:

```text
IsSemicharacterOn H χ Γ :  ∀ γ ∈ Γ, ∀ γ' ∈ Γ,
    χ (γ + γ') = χ γ · χ γ' · exp(−πi · Im H(γ, γ'))
```

The cocycle field of an automorphic factor only needs the law at the one pair being multiplied, so
the new `appellHumbertFactor_cocycle_at` discharges it from the restricted hypothesis; the tree's
`appellHumbertFactor_isMulTwoCocycle` asks for the global form, which is what pulled the vacuity in.
`Γ` is now implicit, determined by `hsemi`.

Ten modules, thirteen hypothesis sites.  **No proof body changed** — the fixes were three
binder-scoping slips and one argument arity, which is what a hypothesis-only defect looks like.  All
ten rebuild green and axiom-clean.  The class of factors the chain speaks about widens from
`{H = 0}` to genuine positive Hermitian forms, which is the class this card is about.

Everything asserted in entries five to fourteen is now true as written; it was not before.

## Lean status 2026-08-22 — unconditional uniform-gap obstruction

`GaloisForLFunctions.HTGeometry.AbeUniformDampingNoGo` is now wired into the HTGeometry umbrella.
Its closed theorem
`not_exists_uniform_negative_re_ee_sub_one` proves, for every real phase `α`, that there is no
constant `c > 0` such that every nonzero natural translate satisfies
`Re(ee(n·α) - 1) ≤ -c`.  The proof uses Mathlib's one-dimensional Dirichlet approximation theorem
and the additive-character chord bound, with no assumptions about a quasi-Abelian factor, seed,
normal convergence, or damping multiplier.  Its exact axiom report is
`[propext, Classical.choice, Quot.sound]`.

This is a closed positive obstruction theorem, not a formalization of the card's public
all-order jet-ampleness claim.  It rules out only the false uniform-majorant route; the two-scale
infinite-tail construction remains the dependency-closed open core, so this card stays in Stage 1.

## Lean status 2026-08-22 — closed concrete positive survivor

`GaloisForLFunctions.HTGeometry.StandardPositiveAppellHumbertJetAmple` supplies a fully concrete
all-order theorem with no analytic or geometric premises: for each `d`, the standard coordinate
Hermitian form and trivial semicharacter define an explicit Appell--Humbert automorphic factor on
`standardIntegerLattice d`, and
`standardPositiveAppellHumbertFactor_jetAmpleEveryFiniteOrder` proves that this one fixed factor
interpolates every finite mixed-jet packet.  The proof constructs the Hermitian, positivity, and
restricted semicharacter certificates rather than accepting them as theorem arguments.

Direct Lean checking and the exact target build passed.  The theorem's axiom report is
`[propext, Classical.choice, Quot.sound]`.  This closes a nontrivial concrete positive case of the
card's intended phenomenon; it is not a substitute for the still-open arbitrary-torusless
quasi-Abelian theorem, whose missing two-scale tail construction prevents a Stage-3 move.

## Rank-zero bounded-seed route is impossible (Lean-closed)

The narrowed finite-disc route still cannot be started by taking the lower factor to be rank zero
and feeding its ordinary entire interpolants into `AbeDampingBoundBridge`.  At rank zero the lower
Hermitian form is zero, so that bridge's normalised estimate is literally

```text
‖seed_B(y)‖ <= C · B^r     for every y in C^d.
```

For each fixed `B` this is a global bound on an entire function.  Liouville therefore makes the
seed constant.  It cannot simultaneously retain a target value `1` and vanish at one nonzero
complement translate.  This is an obstruction to this *route*, not a disproof of the public
all-order theorem: the known positive rank-zero construction uses Gaussian-flat Poincare seeds
directly rather than lower-automorphic bounded seeds.

Lean module `HTGeometry/QuasiAbelianBoundedSeedNoGo` now proves, without added hypotheses:

```text
multivariateEntire_apply_eq_of_norm_le
not_exists_bounded_multivariateEntire_one_zero
not_exists_polynomially_bounded_seed_family_one_zero
```

The exact axiom report of all three is `[propext, Classical.choice, Quot.sound]`; isolated
`lake env lean` and target-only `lake build
GaloisForLFunctions.HTGeometry.QuasiAbelianBoundedSeedNoGo` passed.  Thus the remaining open
producer cannot be an ordinary globally bounded rank-zero seed family.  A valid completion must
construct a different base-to-extension mechanism, or a lower positive factor whose normalised
modulus is controlled without collapsing to a globally bounded entire function.

## Correct pointwise-damping boundary for jets (Lean-closed)

A re-read of Abe §7--§9 identifies why his point-separation limit is valid despite the absence of a
uniform phase gap.  For values, the damping exponential has norm at most `1` on Abe's ray; the
original normally convergent complement series is therefore a parameter-independent summable
dominator, and Tannery/dominated convergence passes the pointwise limit through the full sum.
`HTGeometry/AbeDerivativeDampingNoGo` formalizes that valid abstract step as
`Tendsto (tsum f_B) 0` from pointwise convergence and one summable norm majorant.

That repair does **not** lift to arbitrary jets automatically.  The first derivative already adds a
factor `B`.  With a phase deficit `a > 0`, its size is `B exp(-a B)`.  The closed theorem

```text
not_exists_uniform_linear_exponential_damping_bound
```

proves that no single real constant bounds this expression for all `B >= 0` and all arbitrarily
small `a > 0`.  Its proof chooses `B = (C+1) exp(1)` and `a = B^{-1}`, so no numerical computation
or asymptotic assumption is involved.  Thus pointwise strict negativity plus normal convergence is
sufficient for Abe's value-level argument but insufficient for the derivative-stable domination
needed by the card's all-order jet claim.

The module's axiom report is `[propext, Classical.choice, Quot.sound]`; isolated `lake env lean`
and target-only `lake build GaloisForLFunctions.HTGeometry.AbeDerivativeDampingNoGo` passed.

**Refined open core:** prove a summable phase-degeneracy estimate in Abe's period-matrix coordinates
strong enough to dominate `B^R exp(-B a_gamma)` for every fixed jet order `R`, or construct an
alternative all-order seed family that supplies such a dominator.  Positivity, finite jet
surjectivity, and strict pointwise phase negativity alone cannot provide it.

### Superseding gate ledger (2026-08-22)

The earlier checked boxes headed “Gates” record the invalid proposed proof and are superseded by
this audit.  In particular, “all finite derivatives of complement terms decay” only holds termwise;
it is **not** a proved statement about their infinite Poincare sum.  “subgroup-rank induction lifted
from values to complete finite jet packets” is Lean-proved only under the explicit damping datum,
whose derivative-stable majorant is now identified as unconstructed and not implied by positivity.
Neither item may be used to justify Stage 2 or Stage 3.

## Correct convergence-level extension infrastructure (Lean-closed)

`HTGeometry/QuasiAbelianConvergentDampedExtension` now proves the subgroup-rank determinant
induction from its mathematically minimal analytic output:

```text
AbeConvergentJetPacketLift.remainder_tendsto_zero
```

For every finite packet and every pair of jet indices, this is literal convergence of the actual
complement `tsum` to zero.  The module proves
`AbeConvergentDampedFactorExtension.jetAmpleEveryFiniteOrder` using only that convergence, finite
jet interpolation below the extension, and determinant continuity.  It does **not** assume or
recreate a global `exp(-delta B)` rate.

This is infrastructure, not a new premise for the public theorem and not a completion claim: a
valid period-matrix construction must build these lifts and prove their `remainder_tendsto_zero`
fields.  The prior stronger `AbeDampedJetPacketLift` remains a valid sufficient route but cannot be
silently substituted for that missing construction.

The new theorem has axiom report `[propext, Classical.choice, Quot.sound]`; isolated `lake env lean`
and target-only `lake build GaloisForLFunctions.HTGeometry.QuasiAbelianConvergentDampedExtension`
passed.

### Conjecture `DJS-1` (current construction target)

For each fixed finite packet and jet order `R`, Abe's period-matrix damping ray admits lower seed
columns for which every complement packet-jet term has a parameter-independent summable envelope
and converges pointwise to zero after all derivatives of order at most `R`.  By
`tendsto_tsum_zero_of_pointwise_damping_of_summable_majorant`, this would construct the
`remainder_tendsto_zero` field of `AbeConvergentJetPacketLift`; the new convergence-level extension
would then complete the subgroup-rank induction.

`DJS-1` is **not proved**.  The uniform-phase-gap and globally bounded rank-zero variants are
Lean-refuted above.  Any proof must exploit quantitative structure of Abe's actual period matrix
and seed functions beyond strict nonresonance.

## Primary-literature audit extension (2026-08-22)

Three independent primary sources now delimit the known result precisely.

1. Abe, *Construction of automorphic forms for ample factors of quasi-Abelian
   varieties*, Kyushu J. Math. 57 (2003), Theorems 8.1 and 9.1, constructs sections
   separating finite reduced point sets and one tangent direction.  Its §9
   differentiation argument does not state a summable all-order complement-jet
   majorant.
2. Capocasa--Catanese, *Linear systems on quasi-abelian varieties*, Math. Ann.
   301 (1995), Theorem A, proves that a positive line bundle has nonzero sections,
   infinite-dimensional in the noncompact case.  Its embedding results concern
   base-point freedom or projective embedding under divisibility/reducibility
   conditions; the paper contains no finite-Artin-jet surjectivity result.
3. Ghanmi--Intissar--Souid El Ainin, *On holomorphic theta functions associated
   to rank \(r\) isotropic discrete subgroups of a \(g\)-dimensional complex space*,
   arXiv:1506.06353, constructs an explicit reproducing-kernel Fock theta space
   only for a positive-definite Hermitian form and an isotropic subgroup of rank
   \(r\le g\).  This is a restrictive special model, not the general
   quasi-Abelian period-matrix setting of this card; it supplies no proof of
   `DJS-1`.

Thus the external audit neither proves nor refutes the public theorem.  It does
confirm that replacing `DJS-1` by “infinite-dimensional section space” or by
very ampleness would be an invalid implication.  The theorem remains **Stage 1**
until the derivative-stable Poincare-tail construction is paper-proved and then
formalized without assumptions.

## Super-Gaussian small-divisor boundary (Lean-closed)

The two-scale finite-disc route needs a quantitative seed construction, not merely
an unspecified Gaussian factor in the complement index.  The new closed theorem
`HTGeometry/AbeGaussianSmallDivisorNoGo`

```text
not_exists_gaussian_small_divisor_uniform_damping_bound
```

proves that there is no constant `C` bounding, simultaneously for all `B >= 0`
and all natural `n`,

```text
B · exp(-n^2) · exp(-B · exp(-n^3)).
```

At `B = exp(n^3)` this term is exactly `exp(n^3 - n^2 - 1)` and is unbounded.
Thus even a Gaussian lattice amplitude cannot provide a derivative-stable envelope
when a phase deficit is permitted to be super-Gaussianly small in its lattice
index.  The result has no premises and its axiom report is exactly
`[propext, Classical.choice, Quot.sound]`.

This **does not refute the public theorem**: it is a no-go for the claim that
strict phase damping plus a generic Gaussian tail automatically proves `DJS-1`.
A completion must either derive an explicit quantitative lower bound on the
actual period-matrix phase deficits, or build seeds whose dependence on those
small divisors supplies a different summable envelope.

## Period-matrix arithmetic gate: toruslessness is not quantitative

Otiman--Toma, *Hodge decomposition for Cousin groups and for
Oeljeklaus--Toma manifolds*, arXiv:1811.02541, Definition 2.4 and its Vogt
examples, distinguish the qualitative Cousin condition from **weak/strong
 dispersiveness**.  For the rank-three lattice in `C^2` with columns

```text
lambda_1 = (0,1),   lambda_2 = (1,alpha),   lambda_3 = (i,0),
```

irrationality of `alpha` makes `C^2 / Lambda_alpha` a Cousin group, while
Vogt's explicit Liouville choice is not even weakly dispersive.  Weak
 dispersiveness is exactly an exponential lower bound on `|q alpha - p|`;
it is an extra arithmetic condition, not a consequence of irrationality.

This family lies inside the geometric scope relevant here.  With the standard
positive Hermitian form

```text
H((z,w),(z',w')) = z·conj(z') + w·conj(w'),
```

its imaginary part on the displayed lattice basis is integral: the only
nonzero pair is `Im H(lambda_2, lambda_3) = -1`.  Hence it is an ample
Riemann form.  It is torusless: if two lattice vectors
`(b+i c, a+alpha b)` and `(b'+i c', a'+alpha b')` spanned a complex line,
separating real and imaginary parts of their determinant and using
irrationality of `alpha` forces all `2 x 2` minors of
`(a,b,c)` and `(a',b',c')` to vanish.  They are real-proportional, so the
line cannot meet the lattice in rank two.

**Route verdict.**  The public theorem is not refuted, but no proof may infer
a derivative-stable `DJS-1` envelope from toruslessness plus strict phase
nonresonance.  The class contains Liouville period matrices with arbitrarily
bad small divisors.  A proof by the current damping ray must add a *proved*
replacement mechanism (not a new public hypothesis): either a seed family
that cancels those divisors, or a wholly different construction.  The
unconditional Lean theorem in `AbeGaussianSmallDivisorNoGo` is the exact
analytic boundary once such deficits are present.

## Normalized multiplier branch: first-jet small divisors remain (Lean-closed)

A local normalization by the nonzero damping multiplier is legitimate for the
finite determinant: multiplying every packet jet block by the inverse local
multiplication matrix preserves invertibility.  It improves the complement
phase factor from a raw derivative factor `B` to `B·|δ|`, where
`δ = exp(2πiθ) - 1`, while value damping is of order
`exp(-B·|δ|²)`.  This is still not a derivative-stable summable envelope under
toruslessness alone.

`HTGeometry/AbeGaussianSmallDivisorNoGo` now additionally proves the closed
unconditional theorem

```text
not_exists_gaussian_normalized_small_divisor_uniform_damping_bound
```

which rules out a uniform bound on

```text
B · exp(-n²) · exp(-n³) · exp(-B · exp(-2n³)).
```

Here `exp(-n²)` is a Gaussian lattice amplitude and
`δ_n = exp(-n³)` is the normalized phase scale.  At
`B = exp(2n³)` the term is exactly `exp(n³ - n² - 1)`, hence unbounded.
The proof is closed in Lean with axiom report
`[propext, Classical.choice, Quot.sound]`; isolated source checking and the
single required target build passed.

Thus local jet normalization removes one phase factor but does not prove
`DJS-1`: the derivative of a holomorphic damping phase is linear in `δ`, while
its real-part loss is quadratic in `|δ|`.  For Liouville period data the
remaining factor defeats a generic Gaussian tail.  Any successful all-order
construction must provide cancellation beyond local multiplier normalization,
or use a genuinely different seed/periodization mechanism.  This is a
no-go for that branch, not a new hypothesis and not a refutation of the
public theorem; the card remains Stage 1.

### Conjecture `DJS-2` — spectral coefficient extraction (unproved)

A possible replacement for the failed real-ray derivative limit is to use the
entire dependence on Abe's damping parameter.  At value level, the complement
sum is an absolutely summable atomic exponential series in `B`; the subgroup
term has phase `t=1` and every complement phase lies on the unit circle away
from `1`.  The peak polynomials

```text
((1 + t) / 2)^N
```

are bounded by `1`, equal `1` at `t=1`, and tend to zero at every other unit
phase.  Applied to the Taylor moments of an identically zero parameter-family,
this isolates the subgroup coefficient without requiring a uniform real-part
gap.

For a jet of order `R`, however, differentiation in the source variable turns
the parameter family into a finite-order spectral distribution:
`B^k exp(B(t-1))` occurs for `k <= R`.  Differentiating the peak polynomial
costs powers of `N`; phases that approach `1` faster than any prescribed rate
can defeat the resulting envelope.  The normalized first-jet no-go above is
the concrete manifestation of this loss.  Therefore the value-level peak
argument does not currently extend to `DJS-1`.

**Current exact target.** Prove an atomic spectral uniqueness theorem for the
specific coefficient families imposed by Abe automorphy that controls these
finite distribution orders, or prove that those coefficient families can
realize the obstruction.  No such theorem is yet proved; no public hypothesis
has been added.

### Revision of `DJS-2`: finite-order atomic peak extraction may close the jet step

The preceding caution about differentiated peak polynomials was incomplete.
For a fixed jet order `R`, suppose the parameter-dependent complement jets have
an absolutely summable atomic expansion

```text
Σ_(λ,k≤R) a_(λ,k) · B^k · exp(B(t_λ - 1)),
|t_λ| ≤ 1,  t_λ != 1,  Σ_(λ,k) |a_(λ,k)| < ∞.             (DJS-2.1)
```

The factor `B^k` is the Laplace transform of a `k`-th derivative of an atom at
`t_λ`.  For the peak `p(t)=(1+t)/2`, differentiation of `p(t)^N` costs at most
`O(N^k |p(t)|^(N-k))`.  Divide the test by `N^R`.  At a target atom `t=1` this
isolates the top derivative order; at every fixed complement atom it tends to
zero, and the normalized derivatives are uniformly bounded.  Absolute
summability therefore gives dominated convergence even when `t_λ -> 1`
super-Gaussianly.  Descending through `R` extracts every target coefficient.

For a determinant block, take the mean of its finitely many phase coordinates;
the closed unit disc is convex and equality in the triangle inequality shows
that the peak `1` occurs only when every selected term is a subgroup term.
Thus the subgroup determinant coefficient is spectrally isolable without a
uniform phase gap.

This avoids the false claim that each differentiated complement **sum** tends
to zero on Abe's real ray.  It instead proves that the evaluation determinant
cannot be identically zero as an entire parameter function, which is all the
induction needs.

**New exact open analytic obligation.** Derive (DJS-2.1), with its finite
source-jet polynomial factors, from Abe's admissible seed class and the normal
Poincare estimates, and carry the finite-order atomic peak-extraction lemma
through the block determinant.  Abe's `rho < 2` growth condition is designed
to absorb every fixed polynomial lattice factor, so this is now a concrete
proof target rather than an unquantified small-divisor condition.  No new
public hypothesis has been introduced.

### `DJS-3` — graded Vandermonde damping determinant (current positive route)

The zero-order target determinant in `DJS-2` is not enough by itself: a local
multiplication matrix has determinant `1`, so finite-order complement spectral
distributions can still mask its constant coefficient.  There is a stronger
construction that forces a nonzero **top** parameter coefficient.

Fix a local damping coordinate `u` with `du(p) != 0`.  Complete `u` to local
coordinates.  For every transverse jet monomial and every `u`-order `r`, take
a lower-automorphic seed that has that transverse target jet and vanishes to
full packet order at earlier blocks.  Lift several copies using distinct
positive damping speeds `c_0,...,c_R`:

```text
seed_alpha · exp(c_j B (u - u(p))).                       (DJS-3.1)
```

At the new target block, the degree-`r` `u`-jet has leading term
`(c_j B)^r/r!`.  The leading evaluation block is Vandermonde in the distinct
`c_j`; tensoring it with the transverse lower-jet basis gives a nonzero
coefficient of `B^D` in the full packet determinant.  At earlier packet blocks
full seed vanishing is preserved by multiplication.

Every complement entry is a finite polynomial in `B` times its phase
exponential.  Expand the finite determinant after termwise Poincare summation
and divide by `B^D`.  The admissible `rho < 2` Poincare estimate supplies an
absolute summable coefficient majorant with every fixed lattice-polynomial
factor.  The normalized complement terms are bounded by that majorant and
converge pointwise to zero along Abe's ray.  Tannery then shows

```text
B^(-D) det M(B)  ->  nonzero Vandermonde target coefficient.
```

Hence `det M(B) != 0` for some finite `B`, without claiming that any
unnormalized differentiated remainder tends to zero.  Super-Gaussian phase
recurrence cannot defeat this leading-coefficient argument because no positive
power of `B` remains after normalization.

**Proof obligations before promotion.** Derive the finite polynomial-exponential
jet expansion and its summable coefficient majorant from Abe's `Phi_2` seed
class; formalize the local-coordinate/Vandermonde jet block; formalize the
normalized determinant Tannery lemma; then instantiate each subgroup-rank
extension.  These are construction obligations, not new public hypotheses.

## Graded damping Vandermonde core (Lean-closed)

`HTGeometry/AbeGradedVandermonde` now formalizes the finite algebraic block of
`DJS-3`.  For distinct complex speeds `c_i` and nonzero parameter `B`, the
matrix

```text
((c_i B)^j)_(i,j)
```

is an invertible Vandermonde matrix.  The closed theorem
`abeGradedVandermonde_det_ne_zero` is proved from Mathlib's exact
Vandermonde determinant formula; its axiom report is
`[propext, Classical.choice, Quot.sound]`, and isolated source checking plus
`lake build GaloisForLFunctions.HTGeometry.AbeGradedVandermonde` passed.

Existing `DampedJetDecay.iteratedDeriv_cexp_mul` identifies these entries with
the jets at a normalization point of the literal damping columns
`w ↦ exp((c_i B) w)`.  The new module is wired into the HTGeometry umbrella.
It proves the local leading block only; the Poincare coefficient expansion and
normalized determinant Tannery argument required by `DJS-3` remain to be
constructed.

## Normalized leading-determinant transfer (Lean-closed)

`HTGeometry/AbeLeadingDeterminant` now proves

```text
eventually_det_ne_zero_of_tendsto_smul_matrix
```

for every finite complex matrix family.  If `s(B) • M(B)` converges to a matrix
with nonzero determinant, then `det M(B) != 0` eventually.  The proof uses
continuity of determinant and the exact identity
`det(s • M) = s^card · det M`; it does not require `s(B)` to be nonzero.

This is the formal transfer endpoint of `DJS-3`: after proving the normalized
Poincare evaluation matrix tends to its nonzero graded-Vandermonde leading
matrix, it yields an actual finite parameter with invertible jet evaluation
matrix.  The theorem is axiom-clean (`[propext, Classical.choice, Quot.sound]`),
was source-checked, target-built with
`lake build GaloisForLFunctions.HTGeometry.AbeLeadingDeterminant`, and wired
into the HTGeometry umbrella.  It is unconditional infrastructure; it does not
supply the still-open normalized Poincare convergence itself.

## Lean progress 2026-08-22 — normalized Tannery core for DJS-3

`HTGeometry/AbeNormalizedDampingTannery.lean` now proves the exact analytic tail statement needed
by the distinct-damping-speed determinant route.  For a summable complex coefficient family
`c_i`, arbitrary strictly positive phases `a_i` (with **no uniform lower bound**), and degrees
`e_i ≤ D`, it defines

```text
B^(-(D-e_i)) exp(-a_i B) c_i
```

and proves its `tsum` tends to zero as `B → +∞`.  The proof is Tannery, but its dominator is
important: for `B ≥ 1`, the normalized scalar has norm at most `1`, so `‖c_i‖` itself is a
summable parameter-independent majorant.  This survives Liouville small divisors; only
pointwise positivity of each phase is used for termwise decay.

The module also proves that this scalar is exactly the degree-`D` normalization

```text
B^(-D) · B^(e_i) exp(-a_i B),
```

when `e_i ≤ D`.  Its two public theorems
`tendsto_tsum_normalizedDampingTerm_zero` and
`normalizedDampingTerm_eq_parameter_normalization` are axiom-clean apart from Lean's standard
`[propext, Classical.choice, Quot.sound]`; target build passed:

```text
lake build GaloisForLFunctions.HTGeometry.AbeNormalizedDampingTannery
```

This closes the previously missing **Tannery consequence** of a finite degree expansion.  It does
not assert such an expansion as a field or hypothesis of the card.  The remaining open core is
still to derive, from Abe's concrete invariant multiplier and `Φ₂` seed estimates, the actual
finite polynomial-in-`B` jet expansion whose coefficients have this summable majorant, and then to
construct the graded target/transverse seed matrix with nonzero Vandermonde leading determinant.

### Correction to DJS-2

The earlier DJS-2 spectral-peak discussion only isolates a possible maximal distribution order.
Without a quantitative accumulation law it does **not** justify recursive extraction of lower
orders or of a constant term.  DJS-3 is the active route: its finite distinct-speed Vandermonde
leading block is nonzero at top degree, and whole-determinant normalization makes every complement
tail subject to the proved normalized Tannery theorem above.

## Lean progress 2026-08-22 — finite graded determinant transfer

`HTGeometry/AbeNormalizedDampingDeterminant.lean` now composes the two closed DJS-3 analytic
pieces.  Its theorem
`eventually_det_ne_zero_of_normalized_damping_matrix_expansion` takes an **actual entrywise
identity** for a finite evaluation matrix after whole-matrix normalization, namely an invertible
leading matrix plus a `tsum` of the normalized polynomial-exponential terms, and concludes that
the original matrix determinant is eventually nonzero.  It uses only strict termwise phase
positivity and entrywise ℓ¹ coefficient summability, not a global damping gap.

This is deliberately a transfer theorem, not a replacement structure field: a completed
quasi-Abelian construction must prove its displayed normalized matrix identity from the explicit
Abe multiplier and its Poincaré series.  The target module build passed and its axiom report is
exactly `[propext, Classical.choice, Quot.sound]`.

### Correction 2026-08-22 — normalization is row graded

A single scalar normalization of the entire packet matrix is generally wrong for DJS-3: jet rows
have different top powers of the damping parameter.  The correct operation is left multiplication
by a finite row-normalization matrix whose diagonal entries are the corresponding inverse powers.

`HTGeometry/AbeLeadingDeterminant.lean` now proves
`eventually_det_ne_zero_of_tendsto_left_mul_matrix`: if a left-normalized matrix tends to an
invertible matrix, then the original matrices are eventually invertible.  No invertibility premise
on the normalizer is needed, since `det(S·M) ≠ 0` already forces `det M ≠ 0`.

`HTGeometry/AbeNormalizedDampingDeterminant.lean` now exposes the exact DJS-3 form,
`eventually_det_ne_zero_of_left_normalized_damping_matrix_expansion`.  It combines that row-graded
determinant transfer with the normalized Tannery theorem.  Both declarations have the standard
clean axiom report `[propext, Classical.choice, Quot.sound]`; targeted module builds passed.

### Lean progress 2026-08-22 — exact local graded block

`HTGeometry/AbeGradedVandermonde.lean` now contains the evaluation-matrix orientation of the
local distinct-speed block.  `abeGradedJetMatrix` has jet orders as rows and damping speeds as
columns; `abeGradedJetRowNormalizer_mul` proves exactly that multiplying the degree-`j` row by
`B^(-j)` turns it into the unit-parameter Vandermonde matrix.  Thus distinct speeds give a
nonzero leading local block after the correct row normalization.  Target build and `#print axioms`
checks passed with only `[propext, Classical.choice, Quot.sound]`.

This closes the local finite linear algebra of DJS-3.  The unsolved bridge is analytic and
geometric: prove that Abe's invariant multiplier has this graded local block simultaneously with
the normalized Poincaré expansion and coefficient summability required by the preceding transfer
theorem.

### Lean progress (exact Abe exponential multiplier)

`AbeExponentialDampingMultiplier.lean` now constructs the actual entire multiplier
`exp (t * (Θ - 1))`, proves its exact pointwise formula, inherits its lower-lattice invariance from
`Θ`, and proves that it equals one at every point where `Θ = 1`.  The targeted module build and
`#print axioms` audit close with only Lean's standard logical axioms.

This is an exact input to the proposed distinct-speed packet construction.  It does **not** yet
supply the required all-order jet expansion, seed estimates, or global finite-jet interpolation;
therefore it provides no basis for advancing this card from Stage 1.

### Lean progress (unconditional multiplier jet transport)

The exact Abe multiplier now has a closed directional derivative identity and an all-order finite-jet
vanishing equivalence: multiplication by `exp(t * (Θ - 1))` neither creates nor erases vanishing
jets of any prescribed finite order.  This uses the multiplier's explicit inverse at `-t`, not a
nonvanishing hypothesis.  The changed leaf module
`GaloisForLFunctions.HTGeometry.AbeExponentialDampingMultiplier` passed its targeted build; the two
new declarations passed `#print axioms` with only `propext`, `Classical.choice`, and `Quot.sound`.

This closes one genuine all-order local transport component.  It does not establish the card's
missing global Poincare jet expansion or all-order interpolation theorem, so Stage 3 is still not
justified.

### Lean progress (all-order exponential jet recurrence)

`AbeExponentialDampingJetRecurrence.lean` now proves, without any analytic premise, that every
repeated derivative in a fixed complex direction of Abe's literal multiplier factors as the
multiplier times a recursively defined finite jet factor.  Each recursion step has exactly one
new `t · ∂Θ` term and one differentiated prior factor; this is the algebraic source of the finite
polynomial dependence on the damping time needed in `DJS-3`.

The leaf source check, targeted build, and axiom reports for both public recurrence theorems passed
with only `[propext, Classical.choice, Quot.sound]`.  This does not yet bound the recursively
produced coefficient sources on complement translates, nor prove their Poincare summability.

### Lean progress (all-order damped-seed jet recurrence)

`AbeExponentialDampingJetRecurrence.lean` now also gives the exact all-order recurrence for
`exp(t * (Θ - 1)) · seed`.  Thus every repeated directional seed jet, before translation into a
Poincare summand, is literally the exponential multiplier times a finite recursively generated
source.  No seed-growth, phase-gap, or summability field was assumed.  The changed leaf source
check and targeted build passed; the new public theorem's axiom report is
`[propext, Classical.choice, Quot.sound]`.

The remaining step is quantitative: derive a summable complement-translate majorant for these
recursively generated coefficient sources from the concrete quasi-Abelian seed construction.

### Lean progress (finite polynomial all-order jet factor)

`AbeExponentialDampingJetPolynomial.lean` now proves unconditionally that the recursive factor
left after any fixed number of directional derivatives of Abe's literal multiplier is a finite
source-valued polynomial in the damping parameter.  The proof derives complex linearity of the
entire-source directional derivative, expands the finite source polynomial, and uses a sum-type
index to combine the degree-raised multiplication term with the differentiated coefficient term.
It introduces no analytic, geometric, seed-growth, or summability assumption.

The leaf source check and targeted module build passed.  The new public polynomiality theorem has
axiom report `[propext, Classical.choice, Quot.sound]`.  This is only the finite algebraic part of
DJS-3: the card still lacks a derivation from concrete quasi-Abelian/Poincare data of bounds and
an ℓ¹ majorant for the resulting translated coefficient sources.  Hence this progress does not
justify moving the card to Stage 3.

### Lean progress (finite polynomial all-order damped-seed factor)

The same module now proves the exact finite-polynomial statement for every all-order damped-seed
jet factor, with arbitrary concrete seed as its degree-zero coefficient.  Combined with the prior
factorization of the derivative of `exp(t * (Θ - 1)) · seed`, this isolates all damping-parameter
dependence in finitely many explicit source coefficients at each fixed jet order.  The updated leaf
source check and targeted build passed; this new theorem's axiom report is
`[propext, Classical.choice, Quot.sound]`.

This still does not control translated coefficient norms or establish the needed Poincare ℓ¹
majorant from quasi-Abelian geometry, so Stage 3 remains unavailable.

## Research checkpoint 2026-08-22 — `DJS-3M` derivative-stable convergence route

**[LITERATURE]** The primary source is Abe, *Construction of automorphic forms for ample factors
of quasi-Abelian varieties*, Kyushu J. Math. 57 (2003), 51–85,
DOI `10.2206/kyushujm.57.51`.  Its Section 7 defines the convergence property of a seed `f` as
compact convergence of the Poincare series for `f·phi` for every `phi` in Abe's subquadratic
class `Phi_2`.  Proposition 8.2 constructs finite point separators from such a seed; Theorem 8.1
uses a pointwise complement damping limit; Theorem 9.1 proves one tangent-direction separation.
No all-order Artin-jet statement or derivative-stable tail majorant is stated there.

**[CONJECTURE — DJS-3M]** In Abe's actual period-matrix coordinates, every fixed finite spatial
jet of a damped Poincare summand admits a finite polynomial-exponential expansion whose coefficient
Poincare series are locally normally summable.  More exactly, the coefficient sources are the
finite products of the original `f·phi` with derivatives of the coordinate character `E`; they
remain in the `Phi_2` convergence class, while the residual damping exponential is handled termwise
by the normalized Tannery theorem already formalized here.

**Hostile audit.** Convergence property alone does not imply DJS-3M: `exp(C·E)` need not itself
belong to `Phi_2`, so treating the damped series as another undamped convergence-property series is
circular.  The potential structural escape is that Abe's complement coordinate should satisfy the
period-matrix identity `|E(gamma_w'')| = 1`.  If derived, this makes the literal damping multiplier
bounded independently of the complement index on each fixed compact set for every fixed parameter,
and `E^q·phi` remains in `Phi_2` for each finite `q`.  This defeats the circularity without a new
public hypothesis.

**[OPEN CORE]** Prove those two coordinate consequences directly from Abe's period matrix, then
prove the resulting compact-normal coefficient expansion and preserve the `f·Phi_2` representation
through the enlarged-packet induction.  This remains unproved; `DJS-3M` therefore has verdict
`SURVIVES PRELIMINARY ATTACK`, not `[PAPER-PROVED]`.

### `DJS-3M` primary-source refinement

Abe's displayed toroidal period matrix has a real `R2` block, while
`E(t)=exp(2π i t)`.  Thus the relevant complement coordinate shift is real and satisfies
`|E(gamma_w'')|=1`; it need not equal one, so irrational shifts still give the already-proved
no-uniform-gap obstruction.  This is the key distinction: it gives an index-uniform **modulus**
bound for the damping multiplier on any fixed compact set, but never a uniform negative real-part
bound along the damping ray.

Consequently, for fixed damping parameter, the multiplier belongs to the same subquadratic
translation-growth class `Phi_2`; finite products with `E^q` remain there.  The convergence property
therefore normally sums every coefficient source.  Cauchy estimates on a slightly larger compact
then give an ℓ¹ coefficient majorant for every fixed spatial derivative.  This is the viable
mechanism behind DJS-3M and is compatible with small divisors.

**[OPEN CORE, narrowed]** Write and audit the full structured subgroup-rank induction: its invariant
must retain a `f·Phi_2` presentation while it realizes the prescribed finite local algebra; then
formalize the concrete toroidal period-matrix model, the `Phi_2` closure and Cauchy-majorant bridge,
and the tensor graded-Vandermonde block.  No analytic majorant is now to be assumed as a structure
field.  The paper proof is not yet dependency-closed because this induction invariant and the
coordinate-to-Lean translation have not yet been written in full.

### Lean progress (real-period damping modulus bridge)

`AbeRealCoordinateDamping.lean` now formalizes the exact elementary period-coordinate fact used by
DJS-3M.  For `E(z)=exp(2π i z)`, every real translation multiplies `E` by a unit additive
character and hence preserves its modulus.  The literal damping factor
`exp(t * (E(z+r)-omega))` consequently has an explicit bound independent of the real shift `r`.
This proves the modulus control supplied by Abe's real `R2` coordinate block while making no
uniform negative-phase assertion.

The leaf source check and targeted build passed; its new public bound has axiom report
`[propext, Classical.choice, Quot.sound]`.  It is one concrete component of the missing `Phi_2`
closure/normal-convergence bridge, not the all-order jet-ampleness theorem itself.

### Lean progress (transverse graded Vandermonde block)

`AbeTransverseGradedVandermonde.lean` now tensors the existing distinguished-coordinate graded
Vandermonde matrix with an arbitrary finite transverse identity block.  It proves exact row-scale
normalization and determinant nonvanishing whenever the original one-variable nodes are distinct
and its scale is nonzero.  This is unconditional finite local linear algebra, suitable for the
finite transverse packet required by the narrowed `DJS-3M` induction.

The leaf source check and targeted build passed; both new theorem axiom reports are
`[propext, Classical.choice, Quot.sound]`.  It does not provide the missing concrete `Phi_2`
closure, Cauchy-majorant bridge, or subgroup-rank induction, so Stage 3 remains unavailable.

### Lean progress (literal damped Poincaré-summand jets)

`AbeDampedPoincareTermJetExpansion.lean` now proves the exact summand-level bridge needed by
`DJS-3M`: periodizing a seed multiplied by Abe's exponential damping multiplier is identical to
multiplying the undamped Poincaré summand by the exponential multiplier of the **translated**
profile.  Every all-order directional jet is therefore that translated multiplier times an exact
finite recursive source factor, and the source factor has a finite polynomial expansion in the
damping parameter.

This has no analytic premise and no replacement convergence interface.  It reduces the remaining
analytic task to proving local-normal summability and an ℓ¹ majorant for these explicit translated
source coefficients, then carrying the resulting finite packet through the subgroup-rank induction.
The leaf source check and targeted build passed; all four new theorem axiom reports are
`[propext, Classical.choice, Quot.sound]`.  The card remains Stage 1.
