# Reciprocal-period phase reversal and a flat hypertranscendental boundary

- **ID:** `multiple-elliptic-gamma-reciprocal-rank-flat-phase-reversal`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / RECIPROCAL-PERIOD PHASE CLASSIFICATION / SOURCE-PRODUCED FLAT CLASS
- **Source:** `../3-formalized/all-parameter-multiple-elliptic-gamma-dichotomy.md`;
  `../3-formalized/not_new_scientific_knowledge/elliptic-gamma-source-face-fracture.md`;
  `../1-in-progress/hypertranscendental-bornological-krull-radical.md`
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[EXTERNAL EXACT-MATCH SEARCH NEGATIVE] [NOT AN RH RESULT]`
- **Statement:** Componentwise reciprocalization of a rank-two period family can change its empty
  hypertranscendence graph into a complete graph of arbitrary size.  Along a rational cofinal
  scaling, the resulting hypertranscendental multiple elliptic Gamma functions differ from their
  differentially algebraic zero-nome face by a nonzero all-orders-flat source section.

## Goal

Produce an actual special-function element in the bornological Krull radical, rather than selecting
the ambient witness `exp(-1/|w|)` after the target algebra is known.  The theorem must also detect
genuine differential phase: every finite fibre on one side is differentially algebraic in `z`,
while every reciprocal fibre of order at least one is hypertranscendental in the same variable.

This is a theorem about a reciprocal-period Cremona transform.  It is **not** asserted to be one
global Narukawa modular transformation.  A Jacobi `S`-move on an individual theta face also
rescales `z`, and the different face normalizations do not assemble into one common modular chart.
That non-gluing boundary is part of the result, not silently removed.

## Exact theorem

Fix `N>=2`, distinct integers `n_1,...,n_N`, and a transcendental
`omega` in the complex upper half-plane; one may take `omega=i*pi`.  Put

```text
tau_j=omega+n_j,
alpha_j(m)=tau_j/m,
beta_j(m)=-1/alpha_j(m)=-m/tau_j,              m>=1.       (1)
```

Both period families lie in the upper half-plane.  Let `G_alpha(m)` and `G_beta(m)` be the
`N`-period multiple elliptic Gamma functions in the parity-correct normalization of the
all-parameter dichotomy paper.  Then:

```text
rank_Q span_Q{1,alpha_1(m),...,alpha_N(m)}=2,               (2)
rank_Q span_Q{1,beta_1(m),...,beta_N(m)}=N+1.               (3)
```

Consequently, for every `m`:

```text
G_alpha(m) and its logarithmic derivative are DA over C(z);
G_beta(m) and its logarithmic derivative are HT over C(z). (4)
```

The face law is exact.  Every nonempty face of the `alpha` family is DA.  In the `beta` family,
every singleton face is DA and every face with at least two surviving periods is HT.  Thus
componentwise reciprocalization changes the empty rank-three graph into the complete graph
`K_N`.

For the flat statement, write

```text
q_j(m)=exp(2*pi*i*beta_j(m)),
x(z)=exp(2*pi*i*z),
Q(m)=product_j q_j(m).                                    (5)
```

Let `K` be the closed disk `|z-i|<=1/4`.  Define the DA zero-nome boundary

```text
B_N(z)=1-x(z)          if N is odd,
B_N(z)=1/(1-x(z))     if N is even.                       (6)
```

There are constants `C>0` and `0<r<1`, depending only on the period packet, such that

```text
sup_(z in K) |G_beta(m)(z)-B_N(z)| <= C r^m               (7)
```

for every sufficiently large `m`.  Put `w_m=1/(m+1)` and

```text
A=ell^infinity({m>=1},C(K)),
D_m=G_beta(m)|_K-B_N|_K.                                  (8)
```

After changing finitely many harmless constants in `(7)`, `D` is a bounded sequence and

```text
D != 0,
D belongs to intersection_(k>=1) w^k A.                  (9)
```

In fact every coordinate `D_m` is nonzero.  Hence the actual multiple elliptic Gamma source
supplies a nonzero flat section whose fibres are the difference between an HT function and its
DA boundary.  Every finite inverse-power boundary jet is identical to that of `B_N`, although the
exact fibre remains hypertranscendental.

## Paper proof

### Reciprocal rank

Equation `(2)` is immediate from

```text
alpha_j(m)=omega/m+n_j/m in span_Q{1,omega}.
```

The span has dimension two because `alpha_j(m)` is nonreal.

For `(3)`, suppose

```text
c_0+sum_j c_j/(omega+n_j)=0,                 c_j in Q.    (10)
```

Multiplying by `P(omega)`, where

```text
P(X)=product_j (X+n_j),
```

gives the value at `omega` of a polynomial over `Q`:

```text
c_0 P(X)+sum_j c_j P(X)/(X+n_j).                         (11)
```

Transcendence of `omega` forces this polynomial to vanish identically.  Evaluation at
`X=-n_k` gives

```text
c_k product_(j!=k)(n_j-n_k)=0,
```

so every `c_k` is zero, and then `c_0=0`.  Multiplication by the nonzero rational `-m` does not
change rational rank.  This proves `(3)`, including the same statement for every subpacket.
The exact all-parameter period-rank dichotomy gives `(4)` and the graph classification.

### Exponentially flat zero-nome degeneration

Since

```text
Im(-1/tau_j)>0,
|q_j(m)|=exp(-2*pi*m*Im(-1/tau_j)),
```

there is an `r<1` with `|q_j(m)|<=r^m` for every `j,m`.  Put `t_m=r^m`.  The multi-index tail obeys

```text
S_m=sum_(nu in N^N,nu!=0) |q(m)^nu|
   =product_j (1-|q_j(m)|)^(-1)-1
   <= (1-t_m)^(-N)-1
   =O(t_m).                                                (12)
```

On `K`, `x` is bounded and bounded away from zero, while `|x|<1`.  The denominator-side product
therefore splits as

```text
(x;q(m))_infinity^(N)
  =(1-x) product_(nu!=0)(1-x q(m)^nu)
  =(1-x)(1+O(t_m))                                        (13)
```

uniformly on `K`.  The standard infinite-product estimate

```text
|product_a (1+u_a)-1| <= exp(sum_a |u_a|)-1
```

applies because `(12)` is summable.

For the numerator-side product,

```text
sum_nu |Q(m)q(m)^nu/x|
 <= |Q(m)| inf_K|x|^(-1) product_j(1-|q_j(m)|)^(-1)
 =O(t_m^N),
```

so

```text
(Q(m)/x;q(m))_infinity^(N)=1+O(t_m)                       (14)
```

uniformly on `K`.  Substitution of `(13)`--`(14)` into the parity-correct product gives `(6)`--`(7)`.

For every `k`,

```text
sup_m (m+1)^k r^m < infinity,
```

so `(7)` proves `D in w^k A`.  This holds for all `k`.

Finally, if `D_m` vanished on `K`, the identity theorem would make `G_beta(m)=B_N` as meromorphic
functions.  The right side is DA, contradicting `(4)`.  Thus every `D_m` is nonzero, proving `(9)`.
`QED`

## What is new and what is parent mathematics

Parent inputs:

- componentwise inversion and partial-fraction independence are elementary;
- trigonometric/zero-nome degeneration of elliptic Gamma products is classical;
- exponentially small nome tails and flat functions are standard asymptotic analysis;
- modular/resurgent `q`-Pochhammer sectors are already studied in the literature;
- failure of Krull intersection in bounded function algebras is parent function-algebra theory.

The candidate-new theorem is their coupling through the exact all-parameter multiple elliptic Gamma
dichotomy:

```text
empty DA graph
  --componentwise reciprocal period transform-->
complete HT graph of arbitrary size
  --zero-nome completion-->
nonzero all-orders-flat deformation of one DA boundary.   (15)
```

No located paper states `(15)`, classifies its face graph, or exhibits the difference between the
named HT fibre and its DA degeneration as an element of the bornological Krull radical.  Exact,
stronger, equivalent, and mechanism searches through July 2026 found only the parent modularity,
degeneration, resurgence, and function-algebra results.

Primary adjacent sources:

- A. Narukawa, *The modular properties and the integral representations of the multiple elliptic
  gamma functions*, <https://arxiv.org/abs/math/0306164>.
- G. Felder and A. Varchenko, *The elliptic gamma function and `SL(3,Z) x Z^3`*,
  <https://arxiv.org/abs/math/9907061>.
- V. Fantini and C. Rella, *Modular resurgence, q-Pochhammer symbols, and quantum operators from
  mirror curves*, <https://arxiv.org/abs/2506.08265>.
- R. Mortini, R. Rupp, and A. Sasane, *On the Krull Intersection Theorem in Function Algebras*,
  <https://arxiv.org/abs/1605.08204>.

## Hostile significance audit

- **Not one modular symmetry.** The reciprocal transform acts componentwise on period labels.
  Genuine Narukawa projective charts divide all periods and `z` by one common period and preserve
  augmented rational rank.  Calling `(15)` a global modular phase change would be false.
- **Same differential axis.** Statements `(2)`--`(4)` all concern differential algebraicity in
  `z`; the theorem does not compare `z`-differential rank with parameter-space algebraic rank.
- **Family statement.** Flatness concerns the cofinal source family indexed by `m`, not one fixed
  function becoming DA.
- **Actual source class.** `D` is obtained from the named multiple elliptic Gamma product and its
  exact zero-nome face.  It is not the ambient witness `exp(-1/|w|)` inserted after choosing the
  receiver.
- **No `BCDef_F` overclaim.** The theorem provides the explicit source-produced element demanded
  by the completion programme, but it does not construct the comparison functor
  `L chi_F^*(Comp_F C_F) -> Comp_F(L chi_F^* C_F)` or compute its cofiber.
- **No RH claim.** Flat HT capacity supplies neither divisor orientation nor Pick-kernel
  domination.  It only proves that finite boundary jets cannot certify that the completed source
  stayed in the DA phase.

## RH pressure test

The Xi completion architecture already excludes every finite reporter and reduces the live core to
a source-pure all-aperture Pick comparison.  The theorem adds one exact necessity:

```text
a comparison built only from finite inverse-aperture jets cannot distinguish
an HT reciprocal-period completion from its DA zero-nome boundary.          (16)
```

The direct Xi sewing does not satisfy that antecedent.  The multiple-Gamma theorem differentiates
in the additive/fugacity variable with fixed nomes, whereas the Xi spectral derivative moves every
nome \(q_p=p^{-s}\).  Diagonal Dedekind-eta specialization also inserts partition multiplicities
not present in one Euler ray.  Taking the first fugacity coefficient recovers the Euler packet but
throws away the full HT carrier.  Plethystic Möbius inversion repairs the coefficient sequence, but
its Mellin multiplier is the existing \(1/\zeta(s)\) continuation wall; analytic-unit twists do not
make that wall easier.

The strongest positive survivor is now proved separately in
`prime-completion-annihilates-hypertranscendence-at-even-temperature.md`.  It retains every
occupation mode: finite prime packets are HT, their complete logarithmic normal jets are the finite
Euler packets, yet all-prime completion at every even integer exponent is DA by Gamma reflection.
Therefore even source purity plus convergence of the entire boundary germ does not conserve the HT
phase.  A valid RH bridge must transport a completion-stable polarized invariant, not HT status
alone.  Until such an invariant is constructed, `(16)` remains a constraint rather than progress on
the Xi Pick inequality.

## Lean status

The rank half of the theorem -- equations `(2)`, `(3)` in the form the dichotomy consumes, and the
resulting `(4)` -- is unconditional Lean in
`HTGeometry/EllipticGammaReciprocalRankReversal.lean`:

> **`directPeriod`**, **`inversePeriod`** -- the two families `(ω + n_j)/m` and `-m/(ω + n_j)`;
> **`add_intCast_ne_zero_of_transcendental`** -- a transcendental is not the negative of an integer,
> so the reciprocal family is defined;
> **`partialFraction_independent`** -- **the arithmetic core**: a rational combination of `1`,
> `1/(ω+a)`, `1/(ω+b)` with `a ≠ b` integers vanishes only trivially.  Clearing denominators gives a
> polynomial over `ℚ` vanishing at the transcendental `ω`, hence identically; evaluation at `-a` and
> `-b` kills the two reciprocal coefficients and the remaining constant is killed because
> `ℚ[X]` is a domain;
> **`linearIndependent_inversePeriods`** -- so `1, β_q, β_r` is rationally independent for any two
> distinct labels: the rank-three minor the dichotomy asks for;
> **`not_rankThreeMinor_directPeriods`** -- while `1, α_q, α_r` is always dependent, since
> `α_q - α_r = (n_q - n_r)/m` is rational;
> **`directPeriod_im_pos`**, **`inversePeriod_im_pos`** -- both families lie in the upper half plane
> (`Im(-m/τ) = m·Im τ / |τ|²`);
> **`not_rankThreeMinor_face`** -- a face of a family without a minor has none;
> **`directPeriod_differentialAlgebraic`** -- the direct family has augmented period rank two, and
> both its multiple elliptic Gamma function and the logarithmic derivative are differentially
> algebraic;
> **`inversePeriod_hypertranscendental`** -- the reciprocal family has augmented period rank at
> least three, and both are hypertranscendental;
> **`directPeriodFace_differentialAlgebraic`**, **`inversePeriodFace_hypertranscendental`** -- the
> face law: every nonempty face of the direct family stays differentially algebraic, and every face
> of the reciprocal family with two surviving labels is hypertranscendental.  This is the empty
> graph versus the complete graph `K_N`;
> **`reciprocalPeriod_phase_reversal`** -- **the capstone: componentwise reciprocalization moves the
> family from the differentially algebraic phase to the hypertranscendental one**;
> **`partialFraction_independent_family`** -- the `N`-term partial fraction argument: a rational
> combination of `1` and all the `1/(ω+n_j)` vanishes only trivially, by evaluating the cleared
> polynomial at each `-n_i`;
> **`linearIndependent_inversePeriod_cons`**, **`inversePeriod_augmentedPeriodRank`** -- hence
> **equation `(3)` exactly: the reciprocal augmented period rank is `N+1`**, while the direct one is
> `2` whatever `N` is.

`#print axioms` clean.  The all-parameter dichotomy it consumes
(`MultipleEllipticGammaPeriodRankDichotomy`, `MultipleEllipticGammaFacewiseRankThreeMinor`) was
already unconditional Lean, so nothing is assumed.

The analytic half is under construction, with the reusable estimates already unconditional:

> `HTGeometry/GeometricFlatSequence.lean` -- **`exists_bound_pow_mul_geometric`**,
> **`IsGeometricallySmall`**, **`IsGeometricallySmall.exists_bounded_quotient`**: a sequence bounded
> by `C·r^m` is, for every `k`, the weight `(m+1)^{-k}` times a bounded sequence.  This is `(9)`:
> membership in every power of the ideal generated by `w_m = 1/(m+1)`, i.e. in the bornological
> Krull radical;
> `HTGeometry/InfiniteProductNearOne.lean` -- **`norm_prod_one_add_sub_one_le`**,
> **`prod_one_add_le_exp_sum`**, **`norm_tprod_one_add_sub_one_le`**, and
> **`norm_hasProd_sub_single_le`**: a product of factors near one differs from one, or from a
> distinguished factor, by at most `exp(mass) - 1`.  The argument runs on finite partial products,
> so it needs no group structure on the target -- the multiplicative monoid `ℂ` is not a group, and
> mathlib's product-splitting API is unavailable there;
> `HTGeometry/MultiIndexGeometricTail.lean` -- **`multiIndexHalfSum`**,
> **`tsum_multiIndexMonomial_le_half`**, **`tsum_multiIndex_tail_le`**: this is `(12)`.  Every
> nonzero multi-index carries at least one factor of the nome, so the tail is linear in it, with a
> constant depending only on the number of periods and no closed form for the geometric product;
> `HTGeometry/EllipticGammaZeroNomeDegeneration.lean` -- **`exp_sub_one_le_two_mul`**,
> **`tsum_backwardArgument_tail_le`**, **`norm_backwardProduct_sub_le`** (this is `(13)`),
> **`norm_forwardProduct_sub_one_le`** (this is `(14)`);
> `HTGeometry/EllipticGammaParityDegeneration.lean` -- **`norm_mul_sub_le_of_near`**,
> **`norm_div_sub_inv_le_of_near`**, **`zeroNomeBoundary`**,
> **`norm_product_sub_zeroNomeBoundary_le`**: this is `(6)`, the parity-correct boundary, with the
> quotient case using the same bound to keep the backward product away from zero.

`HTGeometry/EllipticGammaReciprocalNome.lean` supplies the arithmetic of the scaling:

> **`norm_exp_two_pi_I_eq`**, **`norm_ellipticNome_eq`**, **`norm_coordinate_eq`** -- the modulus of
> the exponential coordinate is `exp(-2π·Im)`;
> **`inversePeriod_im`** -- `Im(-m/(ω+n_j)) = m·Im ω/|ω+n_j|²`;
> **`norm_nome_inversePeriod`**, **`exists_nome_bound`** -- hence the reciprocal nome is `b_j^m`
> with `b_j < 1`, and one `r < 1` serves the whole packet: this is the exponential smallness the
> card's `(12)` needs;
> **`flatDisk`**, **`im_bounds_of_mem_flatDisk`**, **`norm_coordinate_le_of_mem`**,
> **`norm_coordinate_ge_of_mem`**, **`norm_one_sub_coordinate_ge_of_mem`**,
> **`norm_one_sub_coordinate_le_of_mem`**, **`one_sub_coordinate_ne_zero_of_mem`** -- on the closed
> disk of radius `1/4` about `i` the coordinate lies in a fixed interval `[X, 1]` and the boundary
> factor `1 - x` in `[W, 2]` with `W > 0`.  No numerical evaluation is used: `exp(-3π/2) < 1`
> because the exponent is negative.

`HTGeometry/EllipticGammaFlatEstimate.lean` closes `(7)` and the flatness:

> **`isGeometricallySmall_of_eventually`** -- geometric smallness beyond a threshold suffices, the
> finitely many initial terms being absorbed into the constant;
> **`flat_massF`**, **`flat_inner_le`**, **`flat_massB`**, **`flat_bw`**, **`flat_aBound`**,
> **`flat_bBound`**, **`flat_max_bound`** -- the whole estimate's arithmetic over abstract bounds,
> isolated so that no nonlinear step ever sees an analytic term;
> **`exists_flat_estimate`** -- **`(7)`: on the disk the multiple elliptic Gamma product differs
> from its parity-correct zero-nome boundary by at most a constant times the nome**;
> **`flat_difference_isGeometricallySmall`** -- combined with the nome bound, the difference along
> the reciprocal family is exponentially small in `m` at every point of the disk, hence by
> `IsGeometricallySmall.exists_bounded_quotient` flat to all orders in the weight `1/(m+1)`.

`#print axioms` clean.

The differential-algebra half of the nonvanishing is now Lean as well
(`HTGeometry/ZeroNomeBoundaryDifferentialAlgebraic.lean`):

> **`differentialAlgebraicOver_of_deriv_quadratic`** -- an element satisfying
> `y' = c₂y² + c₁y + c₀` over the base is differentially algebraic over it, by exhibiting the
> two-variable relation the jet family would have to avoid;
> **`phaseLinear`**, **`coordinateAnalytic`**, **`analyticSubringDeriv_coordinateAnalytic`** -- the
> coordinate `x = exp(2πiz)` as an entire germ, with `x' = 2πi·x`;
> **`zeroNomeAnalytic`**, **`analyticSubringDeriv_zeroNomeAnalytic`**, **`zeroNomeMero`**,
> **`deriv_zeroNomeMero`** -- the boundary `1 - x` in the meromorphic differential field, with
> `y' = 2πi·y - 2πi`;
> **`differentialAlgebraicOver_zeroNomeMero`** -- **the zero-nome boundary is differentially
> algebraic.**

`#print axioms` clean.

`HTGeometry/EllipticGammaFlatNonvanishing.lean` closes the nonvanishing:

> **`polyToAnalytic_C`**, **`ratfunc_algebraMap_complex`**, and the scalar tower -- the two constant
> embeddings into the meromorphic field agree, so **`differentialAlgebraicOver_ratFunc_of_complex`**
> upgrades differential algebraicity over the constants to the coordinate field;
> **`zeroNomeAnalytic_ne_zero`**, **`zeroNomeMero_ne_zero`**,
> **`differentialAlgebraicOver_zeroNomeMeroInv`** -- the inverse boundary satisfies
> `u' = 2πi·u² - 2πi·u`, so both parities of the boundary are differentially algebraic;
> **`eq_of_eqOn_flatDisk`** -- two entire functions agreeing on the disk agree everywhere, the disk
> being a neighbourhood of its centre;
> **`multipleEllipticGammaMero_eq_zeroNomeMero_of_odd`**,
> **`multipleEllipticGammaMero_eq_zeroNomeMeroInv_of_even`** -- hence agreement on the disk forces
> equality in the meromorphic differential field.  In the even case the quotient is cleared first:
> the boundary is nonzero on the disk, so the backward product cannot vanish there either;
> **`exists_flat_difference_ne_zero`** -- **a hypertranscendental fibre differs from its
> differentially algebraic boundary somewhere on the disk, whatever the parity**;
> **`exists_reciprocal_flat_difference_ne_zero`** -- **equation `(9)`: at every scaling parameter
> the reciprocal fibre differs from its zero-nome boundary**, the phase reversal supplying the
> hypertranscendence.

`#print axioms` clean.  The card's analytic chain `(6)`, `(7)`, `(12)`--`(14)` and both halves of
`(9)` are now unconditional Lean, on top of the rank half `(2)`--`(4)`.

## Gates

- [x] 0 → 1 in-progress: exact reciprocal family and flat receiver stated
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] internal corpus collision audit
- [x] external primary-literature exact/stronger/equivalent/mechanism search
- [x] hostile modularity, source-naturality, differential-axis, and RH audits
- [ ] independent specialist priority audit
- [x] 2 → 3 formalized: unconditional Lean rank reversal and flat-product capstone (rank reversal and exact rank `N+1`: `EllipticGammaReciprocalRankReversal`; flat product: `GeometricFlatSequence`, `InfiniteProductNearOne`, `MultiIndexGeometricTail`, `EllipticGammaZeroNomeDegeneration`, `EllipticGammaParityDegeneration`, `EllipticGammaReciprocalNome`, `EllipticGammaFlatEstimate`, `ZeroNomeBoundaryDifferentialAlgebraic`, `EllipticGammaFlatNonvanishing` -- all `#print axioms` clean)
- [x] direct eta/Möbius Xi reciprocal-face sewing falsified
- [x] strongest source-pure positive survivor extracted and paper-proved
- [ ] construct a completion-stable polarized Xi survivor
- [ ] 3 → 4 publication-ready

## Log

- 2026-07-27 — eta modular-dual flat witness found, then demoted as parent resurgence plus an
  elementary Krull-radical embedding.
- 2026-07-27 — naive claim that global modularity changes period rank falsified: genuine projective
  modular charts preserve augmented rational rank.
- 2026-07-27 — extracted the positive survivor: componentwise reciprocalization reverses the exact
  face graph, and rational cusp scaling makes the resulting HT-minus-DA source difference a nonzero
  all-orders-flat section.
- 2026-07-27 — direct eta sewing failed the source and differential-axis audit; Möbius repair
  returned the already formalized RH-equivalent continuation wall.
- 2026-07-27 — source-pure replacement proved: finite prime occupation products are HT, but
  all-prime completion at even temperature is DA while the complete Euler/zeta boundary jet
  survives.
- 2026-08-02 -- the rank reversal is unconditional Lean (`EllipticGammaReciprocalRankReversal`): the
  partial-fraction independence of the reciprocal periods, the rational affine dependence of the
  direct ones, both upper-half-plane conditions, the face law, and the phase-reversal capstone.
- 2026-08-02 -- equations (2)-(4) fully formalized, including the exact reciprocal rank N+1 via the
  N-term partial fraction argument; only the flat degeneration (7)-(9) is left in Lean.
- 2026-08-02 -- the analytic engine of (6), (12), (13), (14) and the Krull-radical half of (9) are
  unconditional Lean; the product estimates are stated for partial products so that the
  non-group monoid C is not an obstacle.
- 2026-08-02 -- (7) proved unconditionally (`EllipticGammaReciprocalNome`,
  `EllipticGammaFlatEstimate`): the product differs from its zero-nome boundary by O(nome) on the
  disk, the reciprocal nome is exponentially small, and the difference is therefore flat to all
  orders. Only the nonvanishing half of (9) is left.
- 2026-08-02 -- the zero-nome boundary is proved differentially algebraic
  (`ZeroNomeBoundaryDifferentialAlgebraic`), via a reusable criterion for first-order quadratic
  differential relations; only the identity-theorem glue of (9) is left.
- 2026-08-02 -- (9) closed (`EllipticGammaFlatNonvanishing`): the identity theorem turns agreement on
  the disk into equality in the meromorphic differential field, and the boundary is differentially
  algebraic in both parities, contradicting the hypertranscendence of the reciprocal fibre. The
  Lean gate of this card is now met.
