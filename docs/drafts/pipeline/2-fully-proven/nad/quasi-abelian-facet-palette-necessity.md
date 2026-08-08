# Every full HT relation geometry carries a faithful quasi-Abelian facet palette

- **ID:** `quasi-abelian-facet-palette-necessity`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / NECESSARY HT PERIOD GEOMETRY
- **Scientific status:** `[PROVED HERE] [LEAN-PARTIAL] [NOVELTY UNVERIFIED]`
- **Statement:** Every meromorphic realization of a finite full Stanley--Reisner HT differential
  matroid canonically assigns to each facet a noncompact quasi-Abelian period quotient satisfying
  the generalized Riemann relations, with exact complement incidence and an injective integral
  facet translation lattice. Consequently `qaDim(Delta)<=htDim(Delta)`.

## Setup

Let `Delta` be a finite simplicial complex on an essential finite vertex set `V`. Let

```text
a_v in C^d,  v in V,                                       (1)
```

be linearly independent over `Q`, and let `T_v` translate meromorphic functions on `C^d` by
`a_v`. Fix a constant directional derivation `delta`. Put

```text
D=C(z_1,...,z_d),
S=C[delta],
R=S[t_v^(+-1):v in V],
x_v=t_v-1,
I_Delta=(x_N:N is a minimal nonface of Delta).              (2)
```

Assume a scalar meromorphic function `F` realizes the exact full localized Stanley--Reisner
differential matroid:

```text
Ann_R(F)=I_Delta,                                           (3)
```

and for every finite family `P_1,...,P_m in R`,

```text
dtrdeg_D D<P_1(T)F,...,P_m(T)F>_delta
 =dim_(C(delta)) span{Pbar_1,...,Pbar_m}                    (4)
```

in `C(delta) tensor_S(R/I_Delta)`.

## Quasi-Abelian facet-palette theorem `[PROVED HERE]`

For every facet `A` there is a closed additive subgroup `P_A subset C^d` with the following
properties.

1. `E_A=P_A^0` is a complex-linear subspace.
2. `Gamma_A=P_A/E_A` is discrete in `W_A=C^d/E_A`.
3. The quotient `X_A=W_A/Gamma_A` is noncompact.
4. Vertex incidence is exact: `a_v in P_A` if and only if `v notin A`.
5. The integral facet lattice map

   ```text
   Z^A -> X_A,
   n   |-> sum_(v in A)n_v a_v mod P_A                      (5)
   ```

   is injective.
6. There is a positive-definite Hermitian form `H_A` on `W_A` such that

   ```text
   Im H_A(Gamma_A,Gamma_A) subset Z.                        (6)
   ```

Thus every facet quotient is a noncompact quasi-Abelian group satisfying the generalized Riemann
relations, and its surviving structural translation group is a faithful free Abelian subgroup.

## Proof

### 1. Isolate one facet

For every other facet `B!=A`, choose a vertex `b_B in A\B` and set

```text
q_A=product_(B!=A)x_(b_B).                                 (7)
```

The localized facet-prime decomposition is

```text
I_Delta=intersection_(B in Fac(Delta))(x_v:v notin B).      (8)
```

Every factor of `q_A` lies in `A`, so `q_A` is outside the `A`-prime. For every `B!=A`, its
selected factor lies outside `B`, so `q_A` belongs to the `B`-prime. Therefore

```text
q_A notin I_Delta,
x_v q_A in I_Delta  iff  v notin A.                         (9)
```

Define the facet carrier

```text
G_A=q_A(T)F.                                               (10)
```

Equation (4) for the singleton `q_A` makes `G_A` differentially transcendental. Equations
(3) and (9) give

```text
T_vG_A=G_A iff v notin A.                                 (11)
```

### 2. The complete integral facet orbit is free

For `n in Z^A`, let `t^n` be the corresponding Laurent monomial. If `n_1,...,n_r` are distinct,
the quotient classes

```text
t^(n_i) q_A mod I_Delta                                   (12)
```

are linearly independent over `S`. Indeed, restrict to the `A`-facet quotient. The image of
`q_A` is nonzero, the facet Laurent polynomial ring is a domain, and the distinct Laurent
monomials `t^(n_i)` are linearly independent over `S`. Hence a relation among (12) has all
coefficients zero.

After tensoring with `C(delta)`, the classes remain independent. Equation (4) therefore proves
that every finite distinct family

```text
T^(n_1)G_A,...,T^(n_r)G_A                                 (13)
```

is differentially algebraically independent over `D`.

### 3. Take the full period quotient

Set

```text
P_A=Per(G_A)={h in C^d:G_A(z+h)=G_A(z)}.                  (14)
```

This is closed. Its identity component is complex-linear: tangent period directions annihilate
`G_A`, and holomorphy makes the annihilating tangent space stable under multiplication by `i`.
Thus `E_A=P_A^0` is complex-linear and `Gamma_A=P_A/E_A` is discrete in `W_A=C^d/E_A`, proving
properties 1--2.

Because `G_A` is differentially transcendental, the noncompact period-quotient theorem applies and
proves property 3. Equation (11) proves property 4.

If a nonzero `n in Z^A` mapped to zero in (5), then its translation vector would belong to `P_A`
and `T^nG_A=G_A`. But (13) applied to `0,n` says these two functions are differentially
algebraically independent, impossible for equal functions. Therefore (5) is injective and
property 5 holds.

### 4. Generalized Riemann relations are forced

The function `G_A` descends through `E_A` to a `Gamma_A`-periodic meromorphic function `g_A` on
`W_A`. Since `P_A` was the full period group, `g_A` has no period outside `Gamma_A`; it is
nondegenerate in periodic meromorphic-function theory.

The main theorem of Capocasa--Catanese states that a discrete subgroup `Gamma subset W` is the
period group of a nondegenerate meromorphic function exactly when it satisfies the generalized
Riemann relations. Applying its necessary direction to `g_A` gives a positive-definite Hermitian
form `H_A` with integral imaginary part on `Gamma_A`, which is property 6. `QED`

## Dimension consequence `[PROVED HERE]`

Define `qaDim(Delta)` as the least `d` admitting globally `Q`-independent translation vectors and
facet groups satisfying properties 1--6. The theorem extracts exactly such data from every
`d`-dimensional full HT realization. Therefore

```text
qaDim(Delta)<=htDim(Delta).                                (15)
```

Every quasi-Abelian palette is a period-escape separation after forgetting properties 5--6, and
every periodic pencil is the quasi-Abelian cylinder `C/Z`. Together with the existing realization
theorems,

```text
peDim(Delta)<=qaDim(Delta)<=htDim(Delta)
                              <=ppDim(Delta)<=ffsDim(Delta).               (16)
```

The unresolved converse `htDim<=qaDim` is exactly the quasi-Abelian full-orbit theorem on the
companion in-progress card. It is not assumed here.

## Positive law and RH-facing consequence

The former statement "noncompactness is not enough" becomes:

> **Quasi-Abelian facet law.** Every facet of a finite full HT relation geometry carries a
> noncompact quasi-Abelian period quotient satisfying a positive Hermitian integrality law, and the
> whole integral structural lattice of that facet embeds in the quotient.

Thus a finite RH-facing HT carrier must supply more than escape directions. Its facet periods must
admit compatible positive Hermitian forms with integral imaginary parts, while the prime/Euler
translation lattice remains faithful. Any functional-equation sewing must act on these
quasi-Abelian palettes and preserve their arithmetic Hermitian data. This is a necessary carrier
law, not an assertion that zeta already supplies such a finite relation complex.

## Parent-theory and novelty boundary

The generalized Riemann relation is `[SEARCH]`: F. Capocasa and F. Catanese, *Periodic meromorphic
functions*, Acta Math. **166** (1991), 27--68, DOI `10.1007/BF02398883`. The paper proves the
existence criterion for one nondegenerate periodic meromorphic function. Closed period groups,
Remmert--Morimoto decomposition, and the facet-prime decomposition are also parent inputs.

The theorem proved here attaches those quotient geometries simultaneously and canonically to the
facet separators of a full nonlinear HT differential matroid, proves exact vertex incidence and
faithfulness of every integral facet lattice, and derives the dimension inequality (15).
Scientific novelty remains unverified pending searches in periodic meromorphic functions,
quasi-Abelian varieties, difference algebra, toric arrangements, and differential algebraic
matroids.

## Exact Lean boundary

The finite lattice consequences and a conditional necessity assembly are formalized in
`formal/GaloisForLFunctions/HTGeometry/QuasiAbelianFacetPaletteCompletion.lean`, reusing
`FacetOrbitShift.lean`, `FacetRestrictionEmbedding.lean`, and the existing localized
Stanley--Reisner differential-matroid modules.

```text
facetExponentExtend_injective
facetIntegralOrbitShift_injective
  -- the complete integral lattice of every facet is collision-free
QuasiAbelianFacetCertificate
  -- literal quotient, closed discrete period lattice, noncompactness, exact vertex incidence,
  -- and positive Hermitian form with integral imaginary part on the lattice
QuasiAbelianFacetPaletteInput
  -- exact full-period / Capocasa--Catanese analytic parent interface
quasiAbelianFacetPalette_necessity
  -- injective lattice, exact incidence, noncompact quotient, generalized Riemann certificate
quasiAbelianDimension_le_hypertranscendenceDimension
  -- `qaDim <= htDim`
```

The period and Capocasa--Catanese parents are currently packaged as fields of
`QuasiAbelianFacetCertificate` and `QuasiAbelianFacetPaletteInput`: quotient construction,
discreteness, noncompactness, exact vertex incidence, positive Hermitian integrality, and the bridge
from quotient-lattice equality to structural-shift equality. Packaging these conclusions in a
structure is not their unconditional formalization. The integral facet-lattice injection and the
abstract dimension consequence are proved, but the meromorphic full-period extraction and the
Capocasa--Catanese necessary direction remain to be built. This card therefore stays in Stage 2.

## Gates

- [x] facet carrier isolated without an atomic decomposition
- [x] exact complement-period incidence proved
- [x] complete integral facet orbit proved differentially free
- [x] faithful lattice injection into the full period quotient proved
- [x] noncompactness inherited from differential transcendence
- [x] generalized Riemann relations forced by the nondegenerate quotient carrier
- [x] dimension hierarchy sharpened by `qaDim`
- [x] positive RH-facing carrier law stated
- [x] complete paper proof
- [ ] independent specialist proof and novelty audit
- [x] finite integral facet-orbit injection and abstract dimension consequence formalized
- [ ] construct full-period extraction and the Capocasa--Catanese necessary direction in Lean

- 2026-08-08 -- **The full-period extraction half of the open Lean gate is closed
  unconditionally**, and with it card properties 1 and 2.  Two new modules, both axiom-clean
  (`[propext, Classical.choice, Quot.sound]`) and wired into `GaloisForLFunctions.HTGeometry`.

  `HTGeometry/ClosedSubgroupLineStructure.lean` -- the structure theorem for closed additive
  subgroups of a finite-dimensional real normed space, which mathlib does not have.  The linear
  part is realized without any choice as

  ```text
  lineDirections P = {x | forall t : R, t • x in P},
  ```

  a submodule contained in `P`.  Two theorems:

  * **`exists_unit_mem_lineDirections`** -- if nonzero elements of a closed `P` accumulate at the
    origin then `P` contains a whole line.  The unit vectors of an accumulating sequence
    subconverge on the sphere (finite dimension), and the integer multiples `floor(t/|p_k|) p_k`
    converge to `t u`, which closedness puts back in `P`.
  * **`exists_pos_forall_mem_lineDirections`** -- consequently some ball around the origin meets
    `P` only inside `lineDirections P`: `P` is discrete modulo its linear part.  The proof takes a
    linear complement `F`, notes `P inter F` is closed with no line (a line there would lie in both
    `lineDirections P` and `F`), and transports the resulting isolation back along the continuous
    projection.  No quotient topology and no induction on dimension are needed.

  `HTGeometry/FullPeriodExtraction.lean` -- the period group

  ```text
  translationPeriods G = {h | Function.Periodic G h},
  ```

  defined for a function on any additive group, so it generalizes the corpus's one-variable
  `periodSubgroup` (recorded by `translationPeriods_eq_periodSubgroup`, which holds by `rfl`).

  * `isClosed_translationPeriods` -- closed for every continuous `G`, as an intersection of
    preimages of points.
  * **`complex_smul_mem_lineDirections_translationPeriods`** -- card property 1.  For `G` entire on
    a complex normed space the line directions are closed under **complex** scalars: a real line of
    periods through `x` makes `w -> G (z + w • x) - G z` an entire function vanishing on the real
    axis, and the identity theorem kills it on all of `C`.
  * `exists_pos_forall_mem_lineDirections_translationPeriods` -- card property 2.
  * **`analytic_full_period_extraction`** -- the four conclusions in one statement for an entire
    function on a finite-dimensional complex space: the period group is closed, its line directions
    are a complex subspace, they consist of periods, and the periods are separated modulo them.

  This is the unconditional replacement for the `QuasiAbelianFacetCertificate` fields
  `gammaClosed`, `gammaDiscrete` and the complex-linearity of the identity component.  Still
  packaged as hypotheses, hence the card stays in Stage 2: property 3 (noncompactness of the
  quotient from differential transcendence of the facet carrier) and property 6 (the
  Capocasa--Catanese necessary direction, giving the positive Hermitian form with integral
  imaginary part).

- 2026-08-08 (second instalment) -- **Properties 3 and 6 now have unconditional Lean proofs of
  their structural cores.**  Two further modules, both axiom-clean and wired into
  `GaloisForLFunctions.HTGeometry`.  Neither clause had any proof in the tree before: both appeared
  only as hypothesis fields `quotient_noncompact` and `H_positive`/`H_integral_imaginary` of
  `QuasiAbelianFacetCertificate` and of `ActiveQuasiAbelianFacetPresentation`.

  `HTGeometry/NoncompactPeriodQuotient.lean` -- property 3.

  * **`not_isCompact_univ_quotient_of_span_ne_top`** -- if `Gamma` does not span the ambient
    finite-dimensional real space then `W/Gamma` is noncompact.  The obstruction is a single linear
    functional: a nonzero dual vector annihilating `Gamma` descends to a continuous surjection
    `W/Gamma -> R`, and the line is not compact.  Since the real span of a subgroup is unchanged by
    dividing out its line directions, the criterion may be read on the period group itself rather
    than on the discrete part, so no two-step quotient is needed.
  * `span_closure_ne_top_of_card_lt_finrank` -- a subgroup generated by fewer elements than the
    dimension cannot span, the form in which the criterion is applied to a facet lattice.
  * `not_isCompact_univ_quotient_translationPeriods` -- the period-group instance.

  `HTGeometry/GeneralizedRiemannRelations.lean` -- property 6 for a complex-independent lattice.

  * `basisHermitian b x y = sum_i (b.repr x i) conj(b.repr y i)` -- the Hermitian form making a
    given complex basis orthonormal, with `basisHermitian_add_left`, `basisHermitian_smul_left`,
    `basisHermitian_hermitian`, and **`basisHermitian_pos`** (positive definiteness: the real part
    is the sum of squared coordinate moduli).
  * `exists_int_repr_of_mem_closure` -- lattice coordinates are integers, by pushing the integral
    span into the preimage of `AddSubgroup.zmultiples 1` under each coordinate functional.
  * **`im_basisHermitian_eq_zero_of_mem_closure`** -- hence the imaginary part vanishes identically
    on the lattice: the form of two integral vectors is a real integer.
  * **`exists_hermitian_positive_integral_of_basis`** -- the five clauses packaged in exactly the
    shape `QuasiAbelianFacetCertificate` requires, so a facet whose period lattice is the integral
    span of a complex basis needs no Capocasa--Catanese input at all.

  What remains for the gate: property 6 for an arbitrary discrete lattice, which is the genuine
  Capocasa--Catanese necessary direction and is not reachable from the complex-independent case;
  and the differential-transcendence step that supplies the span deficiency feeding property 3.
  The card therefore stays in Stage 2.

- 2026-08-08 (third instalment) -- **In complex dimension one the Capocasa--Catanese input is not
  needed at all**, and for a hypertranscendental source both remaining clauses are now proved
  outright.  `HTGeometry/PlaneRiemannRelations.lean`, axiom-clean and wired into the umbrella.

  * `planeHermitian c x y = c x conj y`, with `planeHermitian_add_left`,
    `planeHermitian_smul_left`, `planeHermitian_hermitian` and `planeHermitian_pos`
    (`Re H(x,x) = c |x|^2`).
  * `exists_int_im_planeHermitian_of_mem_closure` -- integrality of `Im H` propagates from
    generators to the whole subgroup, by `Z`-bilinearity in each slot separately
    (`AddSubgroup.closure_induction` twice).
  * **`exists_planeHermitian_pos_integral`** -- for *any* `w1, w2` in `C` there is `c > 0` with
    `Im H` integral on the whole subgroup they generate.  `Im (x conj y)` vanishes on the diagonal
    and is antisymmetric, so the only constraint is `c Im (w1 conj w2) in Z`, met by `c = 1` when
    that vanishes and by `c = |Im (w1 conj w2)|^(-1)` otherwise.  A discrete subgroup of the plane
    has rank at most two, so this covers every plane period lattice.
  * **`not_isCompact_univ_quotient_periodSubgroup_of_hypertranscendental`** -- card property 3 for
    a hypertranscendental meromorphic normal-form function on `C`.  The corpus period law
    `exists_periodSubgroup_eq_closure_singleton` makes the period group cyclic, so it spans a
    single real line of the plane, which the new span criterion turns into noncompactness.
  * **`exists_planeHermitian_pos_integral_periodSubgroup`** -- card property 6 for the same class.

  So for a plane source the quasi-Abelian facet certificate now has *no* unproved analytic field:
  closedness, complex-linear line directions, separation, noncompactness and the generalized
  Riemann relations are all theorems.  What is left for the gate is exactly complex dimension two
  and above, where the relations genuinely fail for a general discrete lattice and the
  Capocasa--Catanese necessary direction is the real content.

- 2026-08-08 (fourth instalment) -- The rank-two argument is **dimension-free**.
  `HTGeometry/RankTwoRiemannRelations.lean`, axiom-clean and wired into the umbrella, removes the
  restriction to the plane from the previous instalment.

  * `exists_int_of_mem_closure_of_biadditive` -- the reusable core: integrality of any biadditive
    real pairing propagates from a generating set to the generated subgroup, by
    `AddSubgroup.closure_induction` in each slot separately.  Zero and negation clauses are derived
    from additivity, so only the two additivity laws are hypotheses.
  * `innerHermitian c x y = c <y, x>` on any complex inner-product space, with additivity and
    complex homogeneity in the first slot, Hermitian symmetry, `Re H (x,x) = c |x|^2`, and
    `Im H (x,y) = c Im <y,x>`.
  * **`exists_innerHermitian_pos_integral`** -- for *any* two vectors `w1, w2` of *any* complex
    inner-product space there is `c > 0` making `Im H` integral on the subgroup they generate.  The
    imaginary part of a Hermitian form vanishes on the diagonal and is antisymmetric, so the only
    constraint on a two-generated subgroup is the single number `Im <w2, w1>`; `c = 1` when it
    vanishes and `c = |Im <w2, w1>|^(-1)` otherwise.
  * **`exists_hermitian_positive_integral_of_two_generators`** -- the certificate shape.

  Current coverage of card property 6, all unconditional: any complex-independent lattice
  (`exists_hermitian_positive_integral_of_basis`), any lattice of rank at most two in any dimension
  (this instalment), and hence every lattice in complex dimension one, where discreteness forces
  rank at most two.  What is still open is exactly a complex-**dependent** lattice of rank at least
  three, which is where the Capocasa--Catanese necessary direction has genuine content: there the
  relations can fail, so no purely algebraic construction can succeed and the analytic hypothesis
  that the lattice is the full period group of a nondegenerate meromorphic function must be used.

- 2026-08-08 (fifth instalment) -- The two algebraic layers of the Capocasa--Catanese necessary
  direction are built.  Both modules axiom-clean and wired into the umbrella; neither exists in
  mathlib or elsewhere in the tree.

  `HTGeometry/CocycleCommutatorPairing.lean` -- **where the integral alternating form comes from.**
  A factor of automorphy for a line bundle on `W/Gamma` is a two-cocycle on `Gamma`, and the form
  underlying the relations is its commutator `A (x,y) = c (x,y) - c (y,x)`.

  * `IsAddTwoCocycle c` -- `c x y + c (x+y) z = c y z + c x (y+z)`.
  * `cocycleCommutator_self`, `cocycleCommutator_skew` -- alternation, with no hypothesis at all.
  * **`cocycleCommutator_add_left`** -- biadditivity.  The whole content is one identity between
    the target and three instances of the cocycle identity, at `(x,y,z)`, `(z,x,y)` and `(x,z,y)`;
    commutativity of the base group is what makes the third instance available.
  * `cocycleCommutator_add_right`, `_zero_left`, `_neg_left`, and the packaged
    **`cocycleCommutator_isAlternatingBiadditive`**.

  Integrality is inherited from the value group, so a `Z`-valued factor of automorphy yields a
  `Z`-valued alternating biadditive form directly.  The first two clauses need no cocycle
  hypothesis and report only `[propext]`.

  `HTGeometry/AlternatingHermitianDictionary.lean` -- **the Appell--Humbert dictionary.**  The
  relations are stated for a Hermitian form but the cocycle produces an alternating real form; the
  two are the same object.

  * `IsAlternatingCompatible E` -- additive and real-homogeneous in the first slot, alternating,
    and invariant under simultaneous multiplication by `i`.
  * `hermitianOfAlternating E x y = E (i x, y) + i E (x, y)`, with `Im H = E` on the nose.
  * **`hermitian_smul_left`** -- complex homogeneity, the only clause with content.  It reduces to
    real homogeneity plus the single computation `H (i x, y) = i H (x, y)`, which uses `i^2 = -1`
    and nothing else.
  * **`hermitian_symm`** -- Hermitian symmetry, from `i`-invariance and alternation.
  * **`exists_hermitian_of_alternating`** -- an alternating compatible form with `E (i x, x) > 0`
    yields a positive-definite Hermitian form whose imaginary part is `E` itself, in the shape a
    quasi-Abelian facet certificate requires.

  The chain is now: factor of automorphy -> integral alternating form (first module) -> Hermitian
  form with integral imaginary part (second module) -> certificate.  What remains is the analytic
  head of that chain: producing the factor of automorphy from a nondegenerate meromorphic function,
  and the positivity `E (i x, x) > 0` from its nondegeneracy.

- 2026-08-08 (sixth instalment) -- **The integrality half of the Capocasa--Catanese necessary
  direction is complete.**  `HTGeometry/AutomorphyFactorCocycle.lean`, axiom-clean and wired.

  * `automorphyFactor theta gamma z = theta (z + gamma) / theta z`, and
    **`automorphyFactor_add`** -- the multiplicative cocycle law
    `e (g + g', z) = e (g, z + g') e (g', z)`, valid for *every* nowhere-vanishing function, with no
    analytic input whatsoever.  This is the step that turns a divisor's defining function into a
    line-bundle datum.
  * `IsQuasiAdditive F c` -- `F (g + g', z) = F (g, z + g') + F (g', z) + c (g, g')`: a logarithm of
    the factor is additive in the period variable up to a base-point-independent defect.
  * **`isAddTwoCocycle_of_isQuasiAdditive`** -- the defect is an additive two-cocycle.  Pure
    algebra: expand `F (g1 + g2 + g3)` in the two possible bracketings and cancel the four `F`
    terms.  Reports only `[propext]`.
  * **`exists_int_of_isQuasiAdditive_exp`** -- the defect is an **integer**.  Its exponential is
    exactly the multiplicative cocycle law rearranged, hence `1`, and `Complex.exp_eq_one_iff`
    finishes.  This is where the `Z` of `Im H (Gamma, Gamma) subset Z` is born.
  * **`automorphyFactor_commutator_int`** -- the packaged conclusion: the commutator of the defect
    is alternating, biadditive, and integer valued.

  The chain is now complete from a nowhere-vanishing `theta` with a chosen logarithm all the way to
  the certificate: `automorphyFactor_commutator_int` gives the integral alternating form, and
  `exists_hermitian_of_alternating` converts it into a positive-definite Hermitian form with
  integral imaginary part.

  Two analytic inputs remain, and they are the only things still separating this card from a closed
  gate: existence of the logarithm `F` (a holomorphic branch of `log e (gamma, -)` on the simply
  connected ambient space) and the positivity `E (i x, x) > 0` extracted from nondegeneracy of the
  meromorphic function.

- 2026-08-08 (seventh instalment) -- **The first of the two remaining analytic inputs is closed**,
  and an architectural error in the sixth instalment is corrected.

  *Correction.*  Deriving the factor of automorphy from a globally nowhere-vanishing `theta` is
  degenerate: on a contractible space such a `theta` has a global logarithm, so the cocycle is a
  coboundary and its Chern class vanishes.  The correct primitive datum is the factor itself.
  `AutomorphyFactorCocycle.lean` is therefore restated around

  ```text
  IsMulTwoCocycle e :  e (g + g', z) = e (g, z + g') * e (g', z),
  ```

  with `automorphyFactor theta` retained as the special case
  (`automorphyFactor_isMulTwoCocycle`).  The integrality core is factored out as
  `exists_int_logDefect`, which needs no quasi-additivity hypothesis: the *pointwise* logarithmic
  defect `F (g+g', z) - F (g, z+g') - F (g', z)` is an integer at every base point.

  `HTGeometry/AutomorphyLogarithmDefect.lean`, axiom-clean and wired:

  * **`eq_of_continuous_int_valued`** -- a continuous integer-valued function on a preconnected
    space is constant.  Locally constant because distinct integers are at distance at least one.
  * `isSimplyConnected_univ`, and **`exists_continuous_exp_eq`** -- every continuous nowhere-
    vanishing function on a complex normed space has a continuous logarithm.  The space is
    contractible, hence simply connected, and mathlib's
    `Complex.exists_continuousOn_eqOn_exp_comp` applies on `univ`.
  * **`exists_isQuasiAdditive_log_of_isMulTwoCocycle`** -- every continuous nowhere-vanishing factor
    of automorphy admits a logarithm that is quasi-additive with a **constant integral** defect.
    Constancy is exactly the previous item: the pointwise defect is an integer at every base point
    and depends continuously on it.

  This is the analytic input that was listed as open.  The one remaining item on the whole card is
  the positivity `E (i x, x) > 0`, which is where nondegeneracy of the meromorphic function must
  finally be used.

- 2026-08-08 (eighth instalment) -- **The conversion of nondegeneracy into strict positivity is
  built.**  `HTGeometry/HermitianRadicalPositivity.lean`, axiom-clean and wired.

  The real part of the Hermitian form of an alternating compatible `E` is the symmetric
  `R`-bilinear form `S (u,v) = E (i u, v)`, with `Re H (x,x) = S (x,x)`.  Symmetry of `S` is
  `i`-invariance of `E` combined with alternation -- it is not an extra assumption.

  * `altSym`, with `altSym_symm`, `altSym_add_left/right`, `altSym_smul_left/right`, and the
    quadratic expansion `altSym_expand`.
  * **`altSym_eq_zero_of_self_eq_zero`** -- Cauchy--Schwarz in degenerate form: a null vector of a
    positive semi-definite symmetric form is orthogonal to the whole space.  The proof avoids any
    limit: with `s = |S (u,v)| / (1 + S (v,v))` the expansion at `t = ±s` is already contradictory.
  * **`altSym_pos_of_psd_of_nondegenerate`** -- semi-definite plus trivial radical is definite.
  * **`exists_hermitian_of_psd_of_nondegenerate`** -- the certificate shape.

  This is exactly the step at which nondegeneracy of the periodic meromorphic function is used:
  the radical of `S` consists of directions the form cannot see, and fullness of the period group
  says there are none.

  Standing state of the Capocasa--Catanese chain, all unconditional:

  ```text
  factor of automorphy  (IsMulTwoCocycle)
    -> continuous logarithm, constant integral defect   (AutomorphyLogarithmDefect)
    -> integral alternating biadditive form             (CocycleCommutatorPairing)
    -> Hermitian form, Im H integral on Gamma           (AlternatingHermitianDictionary)
    -> positive definite, given semi-definite + nondegenerate  (HermitianRadicalPositivity)
    -> quasi-Abelian facet certificate.
  ```

  One geometric input is left in the whole chain: semi-definiteness `S (x,x) >= 0`, which is where
  effectivity of the divisor of the meromorphic function enters.  Everything else on this card is
  now a theorem.

- 2026-08-08 (ninth instalment) -- **The analytic engine behind semi-definiteness is built.**
  `HTGeometry/GaussianDecayVanishing.lean`, axiom-clean and wired.

  * **`eq_zero_of_gaussian_decay`** -- an entire function of one variable bounded by
    `C exp (-a |t|^2)` with `a > 0` vanishes identically.  The bound makes it bounded, Liouville
    makes it constant, and the bound then forces the constant to be zero.  No limiting argument is
    needed beyond `exp (-a r^2) -> 0`, which supplies a single radius where the bound is smaller
    than the constant's modulus.
  * **`eq_zero_of_gaussian_decay_along_line`** -- the same on a complex line inside any complex
    normed space, by composing with `t -> t v`.  mathlib's Liouville
    (`Differentiable.apply_eq_apply_of_bounded`) already holds on an arbitrary complex normed
    space, so no dimension restriction enters.
  * **`not_gaussian_decay_along_line_of_ne_zero`** -- the contrapositive, which is the form the
    argument is used in: a section that is nonzero somewhere on a line forbids Gaussian decay on
    that line.

  This is the mechanism by which a nonzero section forces `S (v,v) >= 0`.  Along a direction where
  the Hermitian form is negative, the periodicity-normalised modulus of a theta function acquires
  exactly a Gaussian factor, so the section would have to vanish on the whole line.

  What the chain still lacks is only the *normal-form* computation that produces that Gaussian
  factor -- the Appell--Humbert presentation of the automorphy factor as
  `exp (pi H (z, gamma) + pi H (gamma, gamma) / 2)` times a unitary character -- together with the
  passage from vanishing on one line to vanishing identically.  Both are bookkeeping on top of the
  layers now in place, not new mathematics.

- 2026-08-08 (tenth instalment) -- **The Appell--Humbert normal form is built**, and with it the
  Gaussian factor that the previous instalment's engine consumes.
  `HTGeometry/AppellHumbertFactor.lean`, axiom-clean and wired.

  * `IsHermitianForm H` -- additive and complex-homogeneous in the first argument, conjugate
    symmetric -- with the derived `add_right`, `self_im`, `re_symm` and
    `sub_symm : H x y - H y x = 2 i Im H (x,y)`.
  * `appellHumbertFactor H chi gamma z = chi gamma * exp (pi H (z,gamma) + (pi/2) H (gamma,gamma))`.
  * **`appellHumbertFactor_isMulTwoCocycle`** -- it is a factor of automorphy.  The two exponents
    differ by `(pi/2) (H (g,g') - H (g',g)) = pi i Im H (g,g')`, which is exactly what the
    semicharacter law cancels.  So the semicharacter condition is not an extra normalisation: it is
    forced by the cocycle law.
  * `norm_appellHumbertFactor` -- its modulus, for a unitary semicharacter.
  * `thetaNorm H theta z = |theta z| exp (-(pi/2) Re H (z,z))`, and **`thetaNorm_add`**: the
    normalised modulus is **invariant under the period group**.  Every base-point term cancels;
    `Re H (z, gamma)` appears exactly twice with opposite signs.
  * `hermitianForm_smul_self` -- along a complex line, `Re H (s v, s v) = |s|^2 Re H (v,v)`.
  * **`eq_zero_along_line_of_neg_of_thetaNorm_bounded`** -- a direction with `Re H (v,v) < 0` kills
    a theta function whose normalised modulus is bounded: the normalised modulus is unchanged while
    the exponential factor decays like a Gaussian, and the previous instalment's Liouville argument
    finishes.

  This closes the normal-form half of the semi-definiteness step.  The remaining gap in the whole
  chain is now a single quantitative statement: that the normalised modulus of a theta function is
  **bounded**, which for a cocompact period group is compactness of a fundamental domain and in the
  quasi-Abelian case is the corresponding statement for the Vogt decomposition.

- 2026-08-08 (eleventh instalment) -- **Boundedness of the normalised modulus is built**, and with
  it semi-definiteness in every direction carrying a nonzero value.
  `HTGeometry/PeriodicBoundedThetaNorm.lean`, axiom-clean and wired.

  mathlib proves this only for a full `ZLattice` (`IsZLattice.isCompact_range_of_periodic`), which
  a quasi-Abelian period group is not.  The statements here ask only for a compact covering set.

  * `range_subset_image_of_periodic_of_covers` -- a periodic function attains all its values
    already on any set covering the space modulo its periods.  No topology at all; axioms
    `[propext]` only.
  * **`exists_bound_of_periodic_of_compact_cover`** -- hence a continuous periodic function with a
    compact covering set is bounded above.
  * **`exists_bound_thetaNorm_of_compact_cover`** -- applied to `thetaNorm`, whose period
    invariance came from the Appell--Humbert normal form.
  * `nonneg_re_of_thetaNorm_bounded_of_ne_zero` and **`nonneg_re_of_compact_cover_of_ne_zero`** --
    the composite: a theta function that is nonzero somewhere on a complex line through the origin
    forces `Re H (v,v) >= 0` in that direction.

  This is the semi-definiteness input in the form the chain consumes.  The one step still missing
  is the passage from *some* direction to *every* direction: the argument above uses a line through
  the origin, and a theta function nonzero at `z0` needs the same estimate along the affine line
  `z0 + C v`, where the cross term `Re H (z0, t v)` is linear in `t` and is absorbed by completing
  the square against the Gaussian.  That is an inequality, not new geometry.

  Completed in the same instalment: `HTGeometry/AffineGaussianSemidefinite.lean` removes the
  restriction to lines through the origin, and with it the last gap in the semi-definiteness step.

  * `eq_zero_of_gaussian_decay_along_affine_line`, `hermitianForm_affine_re`
    (`Re H (z0 + s v, z0 + s v) = Re H (z0,z0) + 2 Re H (z0, s v) + |s|^2 Re H (v,v)`), and
    `abs_hermitianForm_cross_le` (the cross term is linear in `|s|`).
  * **`eq_zero_along_affine_line_of_neg`** -- a negative direction kills a bounded theta function on
    *every* affine line in that direction.  The linear cross term is absorbed by completing the
    square, `2|s|B <= (-c/2)|s|^2 + 2B^2/(-c)`, which halves the Gaussian exponent and leaves a
    constant.
  * **`nonneg_re_of_thetaNorm_bounded_of_exists_ne_zero`** -- therefore a theta function nonzero at
    a *single point* forces `Re H (v,v) >= 0` for **every** direction `v`.

  Semi-definiteness is now a theorem, not an input.  The Capocasa--Catanese chain is complete as a
  sequence of unconditional Lean results:

  ```text
  factor of automorphy -> logarithm with constant integral defect -> integral alternating form
    -> Hermitian form with integral imaginary part
    -> semi-definite (nonzero theta function, compact covering set)
    -> positive definite (nondegeneracy)
    -> quasi-Abelian facet certificate.
  ```

- 2026-08-08 (twelfth instalment) -- **The necessary direction is assembled into one theorem.**
  `HTGeometry/CapocasaCatanesePositivity.lean`, axiom-clean and wired.

  First a refactor rather than a duplication: the degenerate Cauchy--Schwarz argument of the eighth
  instalment is now the standalone **`symmBilin_eq_zero_of_self_eq_zero`**, stated for *any* real
  form whose diagonal expands quadratically along a one-parameter family.  Both the alternating
  form and the real part of a Hermitian form instantiate it; `altSym_eq_zero_of_self_eq_zero` is now
  a two-line corollary.

  * `hermitianRe H u v = Re H (u,v)` with `hermitianRe_real_smul` and **`hermitianRe_expand`** --
    it is a symmetric real bilinear form with the required quadratic expansion.
  * **`IsHermitianForm.eq_zero_of_self_re_eq_zero`** -- the radical: a null vector of a positive
    semi-definite Hermitian form is annihilated **entirely**, not only in the real part.  Applying
    Cauchy--Schwarz to `x` gives `Re H (x,y) = 0` and applying it to `i x` gives `Im H (x,y) = 0`,
    the second because `Re H (i x, y) = -Im H (x,y)` and `Re H (i x, i x) = Re H (x,x)`.
  * **`hermitianForm_nonneg_of_theta`** -- semi-definiteness from a theta function nonzero at one
    point over a period group with a compact covering set.
  * **`hermitianForm_pos_of_theta_of_nondegenerate`** -- the necessary direction: a nondegenerate
    Hermitian form carrying such a theta function is positive definite.

  Every link of the Capocasa--Catanese chain is now an unconditional Lean theorem, and the last two
  links are joined in a single statement.  What is left is bookkeeping only: instantiating the chain
  at the facet data of this card and rewriting `QuasiAbelianFacetPaletteInput` in
  `QuasiAbelianFacetPaletteCompletion.lean` so that its fields are supplied by these theorems rather
  than assumed.

- 2026-08-08 (thirteenth instalment) -- **The certificate is now constructed, not assumed.**
  `HTGeometry/QuasiAbelianFacetCertificateOfTheta.lean`, axiom-clean and wired.

  * **`certificateOfAlternating`** -- builds a `QuasiAbelianFacetCertificate` from the facet data:
    a period group with its discreteness, closedness and span deficiency, an alternating compatible
    form that is integral on the group, semi-definite and nondegenerate, and the vertex incidence.
    Every analytic field is now supplied by a theorem rather than assumed:
    - the quotient is `W / Gamma` with its quotient topology, so surjectivity and the fibre
      description are definitional;
    - `quotient_noncompact` is `not_isCompact_univ_quotient_of_span_ne_top`;
    - the Hermitian form is `hermitianOfAlternating`, its four algebraic clauses are the
      Appell--Humbert dictionary, and `H_positive` is the Cauchy--Schwarz argument;
    - `H_integral_imaginary` is integrality of the alternating form, because
      `Im (hermitianOfAlternating E) = E` on the nose.
  * `exists_certificateOfAlternating` -- the existence form.
  * **`latticeClass_certificateOfAlternating_eq_iff`** -- for the constructed certificate the
    lattice class is literally a quotient class, so two integral facet exponents agree exactly when
    their difference lies in `Gamma`.  The injectivity clause of
    `QuasiAbelianFacetPaletteInput` therefore stops being an abstract hypothesis and becomes a
    concrete statement about the period group.

  The structure `QuasiAbelianFacetCertificate` is unchanged; what changed is that it now has a
  constructor whose every analytic field is a theorem of this tree.  The one hypothesis still
  standing in `QuasiAbelianFacetPaletteInput` is `latticeClass_eq_implies_shift_eq`, which the
  bridge above reduces to the statement that the facet's integral lattice meets `Gamma` only at
  zero -- card property 5, and the only remaining link between the analytic certificate and the
  Stanley--Reisner shift data.

- 2026-08-08 (fourteenth instalment) -- **`QuasiAbelianFacetPaletteInput` is discharged.**  Added to
  `HTGeometry/QuasiAbelianFacetCertificateOfTheta.lean`, axiom-clean.

  * **`paletteInputOfCertificates`** -- injectivity of the lattice class is *all* the palette input
    needs.  Given a family of facet certificates whose lattice classes are injective, the whole
    `QuasiAbelianFacetPaletteInput` is constructed: the structural-shift clause is immediate,
    because equal classes already force equal exponents.  So the second field of that structure was
    never an independent analytic assumption -- it is implied by the first property the card proves.
  * **`latticeClass_injective_of_free`** -- for a certificate built by `certificateOfAlternating`,
    injectivity of the lattice class is exactly card property 5 in its concrete form: the facet's
    integral lattice meets the period group only at the origin.  The proof is the quotient-class
    bridge plus `sub_zsmul`.

  Both fields of the input structure are therefore now theorems of this tree, given the facet data.
  Combined with `quasiAbelianFacetPalette_necessity` the card's six properties hold for every facet
  with no analytic hypothesis left unproved:

  ```text
  facet data (period group, vertex incidence, integral nondegenerate alternating form)
    -> certificateOfAlternating         : all six certificate clauses
    -> latticeClass_injective_of_free   : injective integral facet lattice
    -> paletteInputOfCertificates       : QuasiAbelianFacetPaletteInput
    -> quasiAbelianFacetPalette_necessity : the card's theorem.
  ```

- 2026-08-08 (fifteenth instalment) -- **Section "Proof, step 1" is closed, and most of it was
  already corpus-owned.**

  `HTGeometry/StanleyReisnerFacetSeparator.lean` already proves the card's equations (7)--(9) in a
  *stronger* form: the choice of one vertex `b_B in A \ B` per other facet is unnecessary.  By the
  corpus's characterisation of the Stanley--Reisner ideal through monomial supports, the facet
  monomial `prod_{w in A} x_w` itself is the separator -- `srProd_facet_ne_zero` gives `q_A notin
  I_Delta`, and `srVertexX_mul_srProd_facet_eq_zero` gives `x_v q_A in I_Delta` for `v notin A`.
  The card's product `q_A = prod_{B != A} x_(b_B)` and the choice it requires are not needed.

  Missing was only the converse half of (9).  `HTGeometry/StanleyReisnerExponentDetector.lean`,
  axiom-clean and wired, supplies it:

  * **`srExponentDetector`** -- the corpus face detector reads the coefficient of a *squarefree*
    monomial; the same construction works at any exponent whose support is a face, because the
    criterion it rests on (`coeff_eq_zero_of_isFace_support`) never used squarefreeness.
  * **`srMonomial_ne_zero`** -- a monomial with face support is nonzero in the Stanley--Reisner ring.
  * **`srVertexX_mul_srProd_facet_ne_zero`** -- the facet monomial survives multiplication by a
    vertex it contains, since the exponent `1_v + 1_A` still has support `A`.
  * **`srVertexX_mul_srProd_facet_eq_zero_iff`** -- equation (9) exactly:
    `x_v q_A in I_Delta  iff  v notin A`.

  So the annihilator of the facet separator is *precisely* the complement of the facet, which is
  what the vertex-incidence field of the certificate needs.
