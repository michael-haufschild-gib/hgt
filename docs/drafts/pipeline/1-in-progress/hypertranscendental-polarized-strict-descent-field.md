# The hypertranscendental obstruction field is a polarized strict boundary-colligation field

- **ID:** `hypertranscendental-polarized-strict-descent-field`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL HT CONJECTURE / BIGRADED EFFECTIVITY THEORY
- **Scientific status:** `[CONJECTURE] [GAMMA VERTICAL SEED LEAN-FORMALIZED]`
  `[THREE-CHANNEL HORIZONTAL SEED LEAN-FORMALIZED] [ORIENTATION FALSIFIER PROVED]`
  `[BARE-SOURCE DEGREE-ZERO GATE LEAN-FORMALIZED]`
  `[GAMMA CURVATURE-FORCED STRICTNESS LEAN-FORMALIZED]`
  `[FINITE BOUNDARY-COLLIGATION RECONSTRUCTION LEAN-FORMALIZED]`
  `[HT--DESCENT ORTHOGONALITY PAPER-PROVED; ALGEBRAIC CORE LEAN-FORMALIZED]`
  `[QUASI-ABELIAN PARENT IDENTIFIED] [FIELDS-SCALE OPEN CORE] [NOT AN RH RESULT]`
- **Parents:**
  - `hypertranscendental-source-fracture-hypercube.md`
  - `hypertranscendental-capacity-descent-postnikov-tower.md`
  - `hypertranscendental-conservativity-spectrum.md`
  - `source-framed-galois-colligation.md`

## Verdict

The obstruction field cannot have one degree.

1. A single observability spectrum is too small: three abelian realization channels can be
   pairwise compatible with no common lift before any analytic completion is taken.
2. A single descent/Postnikov object is too small: Gamma is exactly reconstructible at every
   finite clock, but its completed factorial reporter has dense proper range and no continuous
   left inverse.
3. An unpolarized derived object is too small: unit rescaling preserves the complete unframed
   derived physical germ while changing source-labelled orientation.
4. Reconstruction of a preferred HT germ is the wrong universal target: a bare source and any
   fixed finite pointing retain a normalized joint-fixed gauge, and every augmentation factoring
   through that same source is constant on the forgotten gauge fibre.
5. Curvature alone is too small: a perturbation confined to the newly exposed boundary corner
   preserves adjacent-clock curvature.  The lower action, outgoing curvature, and boundary
   self-symbol are jointly necessary and sufficient to reconstruct the next finite source action.
6. Obstruction cohomology is not hypertranscendence: the multiple-Gamma structural facet complex
   can be acyclic while HT persists under arbitrarily deep subcritical source iteration.  An HT
   function can be a global section in `H^0`, not a failure of descent.

These six exact discriminators force one minimal replacement: a **polarized strict
boundary-colligation field attached to the source constraint, not to a canonically selected
solution germ**.  Its cells are enriched incidence fibres and its linear shadow is a bicomplex
with colligation-valued transitions.  Horizontal degree records coherence between incomparable
realization faces.  Vertical degree records whether finite effectivity survives the source-forced
cofinal completion.  Every finite clock cell retains the inherited action, its outgoing
curvature, and its new-boundary self-symbol.  The integral source labels and polarization are
retained as structure, not reconstructed from the unframed derived object.  Individual HT germs
are normalized sections of this field and can form a nontrivial torsor.

This is a compression of the fracture, Postnikov, topology, and observability proposals.  It does
not add a new exception for each failed reconstruction.

## Finite strict-descent diagram

For a source-minimal constrained HT object `x`, a finite observable resolution `N`, and a fracture
face degree `q`, seek source-rigged objects and comparison maps

```text
G_N^q  --A_N^q-->  Y_N^q
 | d_G               | d_Y
 v                   v
G_N^(q+1) --A_N^(q+1)-> Y_N^(q+1),                       (1)
```

where:

- `G_N^q` is the residual source-gauge/coherence object on `q`-faces;
- `Y_N^q` is the corresponding jointly realized boundary object;
- `d_G,d_Y` are the fracture/Čech restriction differentials;
- `A_N^q` is induced by the source anomaly-colligation reporters;
- `d_Y A_N=A_N d_G` is the exact comparison law.

The vertical two-term direction is observation; the horizontal direction is descent.  Neither is
time or a hidden flow.

The finite diagram is not yet the field.  Give every face its source-forced rigging and complete
cofinally in `N`, obtaining `A_hat^q:G_hat^q -> Y_hat^q`.  The three vertical receivers are

```text
K^q=ker(A_hat^q),
S^q=closure(range(A_hat^q))/range(A_hat^q),
C^q=Y_hat^q/closure(range(A_hat^q)).                       (2)
```

`K` is exact blindness, `S` is the strictness or non-Hausdorff defect, and `C` is a genuinely
missing realized direction.  In the quasi-Abelian category of the chosen source-rigged spaces,
`S=0` is exactly the condition that the image morphism is strict.  Formula `(2)` is parent
functional analysis; the candidate-new content is its canonical source assignment and its
interaction with the fracture differential.

## Bare-source degree-zero gate `[PROVED; LEAN]`

For a source action on a differential field `K` and a labelled family of additive reporters
`R_r`, let `Obs_R` record the complete source boundary together with every `R_r`.  Lean proves the
exact maximal theorem

```text
Obs_R injective
  <-> K^S intersect intersection_r ker(R_r) = {0}.          (2a)
```

The equality of two observations is equivalent to their difference being a joint-fixed gauge
annihilated by every reporter.  A nonzero element of the intersection is an explicit
joint-nonconservativity witness.  Consequently any polarization, completion, transport, or
integral datum that factors through the same bare source boundary is constant on the same source
fibre and cannot remove the collision.  The maximal positive domain is the
source-effectively-normalized stratum on which the normalized common kernel is trivial.

This theorem identifies only the degree-zero receiver `K`.  It is not a universal reconstruction
theorem: even when `(2a)` holds, the reporter can be injective with nonclosed range.  Gamma below
lies exactly on that next boundary, with `K=0` but `S!=0`.  Thus gauge normalization is the zeroth
Postnikov gate of strict descent, not its completion.

The Lean declarations are
`familyRealizedBoundaryFingerprint_eq_iff`,
`familyRealizedBoundaryFingerprint_injective_iff`, and
`familyRealizedBoundaryFingerprint_not_injective` in
`formal/GaloisForLFunctions/HTGeometry/JointSourceRealizationConservativity.lean`.

## Exact Gamma vertical seed `[PROVED; LEAN]`

For the Gamma source-normalized factorial reporter, put

```text
(A_N x)_n=x_n/(n+1)!,       n<N.                           (3)
```

Lean now proves, unconditionally:

```text
the raw-stream factorial normalization is a linear equivalence;
the completed reporter is coordinatewise the restriction of that same map;
each completed diagonal coefficient is the oriented curvature of adjacent finite source shadows;
every A_N is bijective;
(A_N^(-1)y)_n=(n+1)! y_n;
the inverse amplification tends to infinity factorially;
A_hat on l2 is injective with dense, proper, nonclosed range;
A_hat has no continuous left inverse.                     (4)
```

Thus every finite vertical complex is split exact, while the completed complex has

```text
K^0=0,       C^0=0,       S^0 != 0.                       (5)
```

This is not a missing finite theorem or a change of algebraic normalization.  The same map is an
equivalence on raw streams and a non-strict monomorphism after source rigging.  It is a strictness
jump at the cofinal boundary.  The finite proof chain succeeds at every stage and still has no
stable global reconstruction.

The curvature assertion is literal.  If `T_N` is the finite Taylor shadow of unit translation,
`p_N` forgets the highest clock, and

```text
Omega_N=p_N T_(N+1)-T_N p_N,                              (5a)
```

then Lean proves coordinatewise

```text
(A_hat x)_n=Omega_(n+1)(e_top)(0) x_n.                    (5b)
```

The same corpus proves that every `Omega_N` has rank one and that the oriented family of all its
boundary vectors uniquely reconstructs the full factorial conormal.  Therefore the coefficients
of `A_hat` are forced by finite source curvature, and on the square-summable clock rigging their
non-strictness follows.  This closes the coefficient-choice loophole but not the rigging-choice
loophole: proving that the relevant completion is source-canonical, or that the defect is invariant
through the full source-admissible rigging class, remains part of the open theorem.

The theorem is formalized in
`formal/GaloisForLFunctions/HTGeometry/GammaCofinalReconstructionDefect.lean` as
`gammaFactorial_finite_effective_completed_nonsplit`.

## Exact horizontal seed `[PROVED; LEAN]`

The two-channel fracture square is exact, but from three channels onward pairwise compatibility
need not imply one common representative.  Lean proves both:

```text
two channels: compatible observations = common lifts;
three channels: pairwise compatible observations can have no common lift;
the exact receiver is M/((I intersection J)+K).            (6)
```

The declarations are `range_birelativeCommonLiftMap_eq_ker`,
`pairwiseCompatible_without_commonTripleRepresentative`, and
`zero_zero_third_has_commonRepresentative_iff` in `FacetRestrictionEmbedding`.

This is a horizontal obstruction with no cofinal limit.  It falsifies any proposal identifying
all HT obstruction with a nonclosed range or singular-value decay.

## Exact HT--descent orthogonality seed `[PAPER PROVED; ALGEBRAIC CORE LEAN]`

The converse identification also fails.  For the generic order-`r` multiple elliptic Gamma
structural module, the augmented coordinate-facet complex is exact in every degree, while the
structural section remains hypertranscendental after arbitrarily many repeated differences in
every set of fewer than `r` transverse source directions.

Thus

```text
horizontal descent acyclic  does not imply  DA,
HT                              does not imply  nonzero higher descent.       (6f)
```

The positive theorem is orthogonality: kinematic local-to-global effectivity and
hypertranscendental capacity are independent coordinates.  The unified field must therefore
retain the enriched incidence fibre

```text
Inc_N^q=Admissible_N^q times^h_(Ambient_N^q) PrimitiveTorsor_N^q             (6g)
```

not merely its obstruction cohomology.  HT sections may live in `H^0`; the remaining question is
whether such a section lies in the pointed, polarized, bornological, integral analytic locus.
The paper theorem and its formal algebraic core are recorded in
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/multiple-gamma-effective-fracture-descent-orthogonality.md`.

## Orientation discriminator `[PROVED NO-GO; POSITIVE STRUCTURE]`

For a pulled-back multiple-Gamma physical characteristic, independently rescaling source cofaces
by analytic units preserves the ideal, fat point, Koszul quasi-isomorphism class, and all homology,
but can reverse source-labelled orientation.

Therefore even the completed unframed derived bicomplex forgets necessary data.  The positive
survivor is not another cohomology group: the integral source frame, logarithmic lift, and
polarization must act on `(1)` before passage to derived equivalence.

## Exact curvature-only no-go and boundary-colligation successor `[PROVED; LEAN]`

Curvature does not determine the finite source action.  Choose a forward clock extension
`i_N:J_N^q -> J_(N+1)^q` with `p_N i_N=1`, and put

```text
Omega_N^q = p_N T_(N+1)^q-T_N^q p_N,
B_N         = 1-i_N p_N,
beta_N^q    = B_N T_(N+1)^q B_N.                          (6b)
```

`Omega_N^q` is outgoing boundary transfer; `beta_N^q` is the self-action wholly inside the new
boundary layer.  Lean proves that adding an arbitrary boundary compression preserves curvature.
Thus a curvature-only theory is false even before completion.

The positive maximal theorem is the exact boundary-colligation identity.  If the higher action is
forward-compatible, then

```text
T_(N+1)^q = i_N T_N^q p_N + i_N Omega_N^q + beta_N^q.     (6c)
```

Consequently the lower action, outgoing curvature, and boundary self-symbol reconstruct the
higher action uniquely.  The declarations are `clockShadowCurvature_add_boundaryCompression`,
`clockShadow_eq_boundaryColligation`, and
`clockShadow_eq_of_curvature_eq_of_boundaryCompression_eq` in `ClockDescentAnomaly`.

This is the finite local cell the unified field must use.  The curvature component can feed a
strictness defect, as Gamma proves in `(5b)`, while the boundary self-symbol retains the flat or
holonomy data curvature cannot see.

Gamma supplies the complete cell, not only its curvature: relative to zero-extension/truncation,
the boundary self-symbol is exactly the identity on the new highest-jet line.  This is proved by
`gammaClockBoundaryCompression_eq_projector`.  Its finite colligation is therefore

```text
(inherited Taylor translation, factorial outgoing transfer, unit boundary self-symbol).
```

## Canonical construction candidate: the boundary-colligation controlled derived limit

At each `(N,q)`, retain the colligation cell

```text
C_N^q=(T_N^q, Omega_N^q, beta_N^q, i_N, p_N)              (6d)
```

together with the enriched incidence fibre `Inc_N^q` from `(6g)`, not a chosen lift or only its
cohomology.  Its inertia is exactly the normalized joint-fixed common kernel `(2a)`.  The candidate
field is the polarized controlled derived limit of these colligation-linked incidence groupoids
over

```text
N^op x Face(source),                                      (6e)
```

in the source-forced quasi-Abelian category.  The linearized mapping cone recovers `(K,S,C)`
vertically and interaction cohomology horizontally.  Changing the splitting `i_N` must act by a
proved colligation gauge equivalence; a chosen splitting is not itself canonical data.

This is stricter than choosing a convenient bicomplex: the indexing category, transition maps,
colligation cells, and admissible riggings must be extracted from the finite source-clock tower.
Gamma already passes the first nontrivial cross-layer test through `(5b)`, `(6c)`, the unit
boundary self-symbol, and boundary tomography.  Construction, splitting independence, and
source-presentation invariance for a general HT source remain conjectural.

## Foundational conjecture

> **[CONJECTURE — POLARIZED STRICT-COLLIGATION DESCENT PRINCIPLE]** Every regular source-minimal
> constrained hypertranscendental system has a canonical, source-presentation-invariant polarized
> controlled derived-limit field `D_S` constructed from the colligation cells `(6d)--(6e)`.  It
> reconstructs the source constraint up to source Morita equivalence, not a preferred solution
> germ.  Its horizontal cohomology gives the complete finite-channel descent and
> higher-interaction obstructions.  Its vertical strictness objects `(K,S,C)` give exact
> blindness, cofinal nonattainment, and missing analytic realization.  Compatible HT germs form
> its normalized section stack.  A pointed analytic section is effective exactly when that stack
> is nonempty, its normalized inertia `(2a)` is trivial, the total colligation object is
> horizontally effective and vertically strict-exact on the required faces, and it admits the
> source-labelled positive real lift.

Vanishing of the obstruction groups does not imply differential algebraicity.  It says that the
incidence problem is effective in the retained enriched category; the resulting global section
may remain hypertranscendental, as `(6f)` proves.

The word `canonical` is load-bearing.  An arbitrarily selected Banach completion, norm, or
polarization does not instantiate the conjecture.

> **[CONJECTURE — HT BOUNDARY-CONCENTRATION LAW]** For every regular finite-source minimal HT
> system, differential hypertranscendence removes every algebraic constraint from the finite
> vertical jet interior.  All effective constraint is carried either horizontally by finite
> source-face relations or vertically by the controlled cofinal boundary colligation
> `(Omega,beta)` of `(6b)--(6d)`, with polarization recording the oriented lift.  Equivalently, the
> finite vertical interior has infinite algebraic clock capacity while the source constraint is
> supported on the strict boundary of the two-index tower.

This is the precise version of “infinite algebraic clock capacity concentrated on a thin
constraint boundary.”  Gamma proves the rank-one/factorial model.  The conjecture is falsified by
any source-minimal HT system with a genuine finite vertical algebraic relation that is neither a
source-face relation nor gauge artefact; such a falsifier would force a new typed receiver.

## Critical hypertranscendence refinement

> **[CONJECTURE — CRITICAL STRICTNESS LAW]** For natural finite-source HT objects, the generic
> completed reporter is vertically conservative but non-strict: `K=0`, `S!=0`, and the source
> constraint is concentrated in a finitely generated horizontal/framing direction.  The
> asymptotic class of the strictness defect, not a finite differential equation, measures the
> rate at which infinite algebraic clock capacity accumulates on the thin boundary.

Gamma realizes the factorial class.  Irrational elliptic Gamma must decide whether adding
independent source directions kills `S`, moves the obstruction horizontally, or merely changes
its decay class.  Multiple Gamma tests whether horizontal constraint depth and vertical
strictness order vary independently.

## Exact period-source transgression seed `[PROVED; LEAN]`

The complete integral-period classification supplies a second natural discriminator.  For every
integral period source `L` in the complex plane, Lean proves the exhaustive dichotomy

```text
period incidence has a continuous left inverse
  <-> L is discrete
  <-> a nonconstant global meromorphic L-fixed gauge exists;

period incidence has no continuous left inverse
  <-> L is nondiscrete
  <-> every global meromorphic L-fixed gauge is constant.   (6a)
```

Hence bare source refinement cannot simultaneously achieve uniform incidence effectivity and
gauge rigidity.  In the discrete phase, attainment is good and automorphisms survive.  In the
nondiscrete phase, automorphisms collapse and attainment fails.  The obstruction does not simply
disappear; it changes representation across the source-topology wall.

This is formalized by
`periodIncidenceMultiplier_hasLeftInverse_iff_exists_nonconstant_fixed`,
`periodIncidenceMultiplier_not_hasLeftInverse_iff_all_fixed_constant`, and
`periodSource_effectivity_gaugeRigidity_dichotomy` in `DiscretePeriodGaugeClassification`.
The period theorem itself is classified as parent mathematics.  Its role here is to force the
shape of the higher conjecture.

> **[CONJECTURE — EFFECTIVITY-DEFECT TRANSGRESSION LAW]** Under a natural refinement of a minimal
> HT source, any residual gauge class that disappears is carried by a canonical connecting map
> into vertical strictness, horizontal interaction, or polarized-lift defect.  The total
> strict-descent class is invariant under the refinement.  It can vanish only when genuinely
> transverse source data are added; adding data functorially generated by the forgotten source
> merely changes the face on which the obstruction is represented.

This is the precise proposed explanation for why independent proof chains repeatedly transport an
unknown rather than remove it.  It is false if “refinement” is allowed to insert an arbitrary
normalization: the morphism must belong to the minimal source category and the connecting map must
be constructed from the strict-descent bicomplex.

## Two filtrations and the proposed obstruction spectral sequences

Passing `D_x` to the left/right Abelian hearts of its quasi-Abelian category should produce two
filtrations of the same total effectivity object:

```text
horizontal first: finite source sewing -> completion strictness,
vertical first:   reporter strictness -> fracture interaction.              (7)
```

> **[CONJECTURE — OBSTRUCTION REPRESENTATION THEOREM]** The two associated spectral sequences
> converge to the same polarized total defect, and the standard analytic obstruction languages
> are conservative edge realizations rather than equal scalar invariants.

This claim is meaningful only after the source functors and exact categories are constructed.  A
generic bicomplex spectral sequence is parent theory and is not new knowledge.

## RH obstruction dictionary `[CONJECTURE; PRESSURE TEST ONLY]`

The seven audited RH terminal classes become distinct failures of one typed object:

| RH terminal class | Strict-descent location |
|---|---|
| O1 source sign/orientation | no positive source-labelled lift of the total class |
| O2 critical all-scale estimate | vertical non-strictness `S` at the critical completion |
| O3 spectral/determinant realization | missing source-natural strict self-dual realization map |
| O4 arithmetic multiplicity | horizontal source relation or higher interaction not produced |
| O5 non-circular comparison | no source-defined morphism from the total object to the divisor reader |
| O6 missing typed bridge | absent exact/conservative realization functor |
| O7 unsupported rigidity | proposed target lies outside the proved source essential image |

The dictionary explains why a finite chain can advance arbitrarily far and still stop: its finite
vertical maps may all be isomorphisms while the critical completion is non-strict, or its
individual realization faces may be valid while total horizontal effectivity fails.

The bare-source theorem imposes a prior typing gate.  A functional equation, reflection law, and
pointing alone cannot carry a canonical zero spectrum while their normalized joint-fixed gauge is
nontrivial.  Before any Hilbert--Pólya or determinant interpretation, a prime--Gamma source must
include genuinely transverse arithmetic data—such as its Dirichlet/Euler coefficient reporter or
an equivalent source-forced normalization—and prove the common-kernel condition `(2a)`.  Data
functorially derived from the bare functional equation cannot substitute for this step.

> **[CONJECTURE; NOT AN RH RESULT]** If a completed prime--Gamma boundary-colligation field is
> constructed before its divisor and its transverse arithmetic reporter kills the normalized
> joint-fixed gauge, the critical zeros are the self-dual support where its polarized total
> realization ceases to be strict-effective.  Reflection pairs this support; confinement to the
> fixed line still requires a genuine source positivity theorem.

## Parent-theory and novelty gate

The following are established parent mathematics:

- quasi-Abelian categories and strict morphisms;
- nonclosed range as failure of strictness in Banach spaces;
- finite-section stability as uniform boundedness of finite inverses;
- bicomplexes, Abelian envelopes, spectral sequences, Čech descent, and fracture diagrams;
- controlled, homotopy, and derived inverse limits;
- polarizations and oriented derived structures.

There are two further parent collisions that materially narrow the claim.  Singer's Gribov theorem
already shows that a gauge orbit space need not admit a continuous global section.  Deformation
and moduli-stack theory already relates automorphisms, deformations, and obstruction classes.
Therefore the generic slogan “a killed gauge reappears as an obstruction” is not new, and neither
is replacing a solution set by a groupoid or stack.

The Gamma theorem `(4)` is an exact natural bridge, not standalone new science.  The three-channel
theorem `(6)` is also parent algebra when source vocabulary is erased.

The possible Fields-scale residue is narrower: construct `D_S` functorially from a minimal HT
source; prove that the colligation tower `(6d)` recovers the constraint up to source Morita
equivalence independently of the chosen splittings; prove presentation invariance; and construct
an HT-specific connecting map whose Gamma, irrational-triptic, and multiple-Gamma specializations
identify exact analytic classes.  The theorem must show that two genuinely distinct obstruction
realizations preserve the same total class.  Generic gauge fixing, generic derived limits, and
generic stack obstruction theory do not supply this source-canonical cross-family law.

Primary parent references checked:

- J.-P. Schneiders, *Quasi-abelian categories and sheaves*, Mémoires SMF 76 (1999),
  `https://www.numdam.org/item/MSMF_1999_2_76__R3_0/`;
- the finite-section literature in which stability means eventual invertibility with uniformly
  bounded inverses, including Lindner--Roch, *The finite section method for random Jacobi
  operators*, `https://arxiv.org/abs/1505.05188`;
- Wallbridge, *Homotopy theory in a quasi-abelian category*,
  `https://arxiv.org/abs/1510.04055`;
- I. M. Singer, *Some remarks on the Gribov ambiguity*, Communications in Mathematical Physics 60
  (1978), `https://doi.org/10.1007/BF01609471`;
- B. Osserman, *Deformations and automorphisms: a framework for globalizing local tangent and
  obstruction spaces*, `https://arxiv.org/abs/0805.4473`.

No source-canonical polarized strict boundary-colligation field for hypertranscendental functions,
nor the claimed joint obstruction-representation theorem, was found in this preliminary pass.
Novelty remains unverified until a theorem is proved and a specialist literature audit is
complete.  A targeted search also found no prior identification of the Gamma finite-clock
translation curvatures with the unique factorial diagonal whose Hilbert completion has dense
nonclosed range; that is a provisional absence finding, not a priority claim.

## Anti-theatre gate

Retire or revise this object if:

1. its quasi-Abelian category is chosen after observing the desired spectrum;
2. `D_S` depends on a nonminimal source presentation or an unquotiented choice of clock splitting;
3. the Gamma strictness jump is not recovered functorially;
4. a boundary self-symbol is discarded although equal curvature does not determine it;
5. the three-channel interaction is not recovered horizontally;
6. orientation still changes under an equivalence declared conservative;
7. the obstruction dictionary consists only of analogies, with no exact realization functors;
8. the total object is just a standard bicomplex or system colligation with HT labels and no new
   theorem.

Every failure has a positive receiver: `K`, `S`, `C`, the boundary self-symbol/flat-holonomy
sector, horizontal interaction cohomology, or the polarized-lift torsor.  A no-go that does not
land in one of these typed receivers falsifies the current completeness conjecture and forces a
new direction, not a renamed component.

## Next theorem targets

1. **Gamma colligation/strictness comparison.** Upgrade `(5b)`, boundary tomography, and the exact
   colligation identity `(6c)` to an equivalence between the periodic-gauge finite-clock pro-object
   and the completed factorial reporter in a source-forced controlled category.
2. **Triptic wall crossing.** Prove how the Gamma `S` class changes when one and then two
   incommensurate translations are added, including the attainment/gauge-rigidity trade.
3. **Multiple-Gamma bidegree theorem.** Compare squarefree horizontal constraint depth with the
   vertical strictness order of the physical-character completion.
4. **Exact realization pair.** Construct two genuinely different analytic obstruction functors
   and prove that they carry the same total class, not merely the same zero set.
5. **Presentation invariance.** Prove invariance under source Morita equivalence and boundedly
   invertible changes of rigging before any zeta specialization.

## Gates

- [x] pure spectral one-axis theory falsified by finite three-channel interaction
- [x] pure descent one-axis theory falsified by Gamma cofinal strictness jump
- [x] unpolarized derived theory falsified by orientation surgery
- [x] Gamma finite-effectivity/completed-nonsplitting theorem Lean-formalized
- [x] Gamma dense proper completed range Lean-formalized
- [x] exact joint-fixed common-kernel gate Lean-formalized
- [x] Gamma completed reporter proved coordinatewise source-curvature-forced
- [x] Gamma oriented finite-boundary tomography of the complete conormal Lean-formalized
- [x] curvature-only reconstruction falsified by invisible boundary compression
- [x] exact finite boundary-colligation reconstruction and uniqueness Lean-formalized
- [x] horizontal three-channel interaction seed Lean-formalized
- [x] HT identified as compatible with acyclic horizontal descent in the multiple-Gamma hierarchy
- [x] quasi-Abelian and finite-section parent theories identified
- [ ] construct the source-canonical controlled derived-limit field for Gamma
- [ ] upgrade the Gamma curvature identity to a functorial pro/completion equivalence
- [ ] prove triptic wall crossing
- [ ] compute one natural multiple-Gamma bidegree
- [ ] construct two conservative obstruction realization functors
- [ ] prove source-presentation invariance
- [ ] complete specialist novelty audit
