# Jet-horizon translation-gauge classification

- **ID:** `jet-horizon-translation-gauge-classification`
- **Stage:** 3-formalized
- **Type:** DIFFERENTIAL-ALGEBRAIC RECONSTRUCTION / GAUGE CLASSIFICATION
- **Scientific status:** `[PROVED ON PAPER] [NOVELTY CANDIDATE] [STRUCTURALLY SIGNIFICANT]`
- **Source:** `nonlinear-rational-observation-curve-horizon-reconstruction`
- **Statement:** For a differential-generic point of an irreducible affine variety, a positive
  derivative horizon loses information at any depth exactly when the variety has a flat additive
  cylinder factor. The lost data form a finite tower of additive integration torsors.

## Set-up

Let `C` be an algebraically closed constant field of characteristic zero and let `U` be a
sufficiently saturated differentially closed extension. Let `Y subset A^m_C` be an irreducible
affine variety of dimension `d`. A tuple `y=(y_1,...,y_m) in Y(U)` is **differential-generic on
Y** when it has no differential-algebraic constraint over `C` beyond the algebraic constraint
`y in Y` and its differentiated consequences. Put

```text
F=C<y_1,...,y_m>,
H_n(Y)=C<delta^n y_1,...,delta^n y_m>,   n>=1,             (1)
A=Stab_trans(Y)={a in G_a^m : Y+a=Y},
K_n=ker(delta^n:U^m -> U^m).                              (2)
```

The group `A` is a linear subspace of `G_a^m`.

## Theorem

### 1. Generic embedding groupoid

For every differential-field embedding

```text
sigma:F -> U   over H_n(Y),
```

the displacement

```text
h_sigma=sigma(y)-y
```

satisfies

```text
h_sigma in A(U) intersection K_n.                         (3)
```

Conversely, if `h in A(U) intersection K_n` and `y` is differential-generic over `C<h>`, then
translation `y |-> y+h` induces an `H_n(Y)`-embedding. Thus generic pairs with the same depth-`n`
horizon are exactly the pairs related by the differential additive translation group
`A(K_n)`.

This is an embedding groupoid in `U`, not in general an ordinary automorphism group of `F`.

### 2. Exact reconstruction criterion

For every `n>=1`,

```text
H_n(Y)=F  iff  A=0.                                       (4)
```

Equivalently, all positive horizon depths have the same binary reconstruction defect: a
translation-rigid algebraic constraint reconstructs its differential-generic point from every
finite-depth derivative tail, whereas an additive cylinder never does.

### 3. Canonical cylinder decomposition

Choose a linear complement `G_a^m=A direct_sum B` and put `Z=Y intersection B`. Translation
invariance gives an algebraic product, not merely a birational one:

```text
Y = A x Z,                  Stab_trans(Z)=0.               (5)
```

Writing the differential-generic point as `y=(a,z)`, equation `(4)` applied to `Z` gives

```text
F=C<a,z>,
H_n(Y)=C<delta^n a,z>.                                    (6)
```

The nonlinear reduced geometry is visible at every depth. Only the coordinates along the
maximal flat additive foliation lose their lower jets.

### 4. Successive-torsor law

For `j>=0`, set

```text
H_j=C<delta^j a,z>.
```

Then each adjacent layer

```text
H_j / H_(j+1)                                              (7)
```

is the Picard--Vessiot additive torsor for

```text
delta X=delta^(j+1)a,
```

with differential Galois group `G_a^r`, where `r=dim A`. Hence a depth-`n` horizon factors its
information loss canonically into `n` successive additive torsors. If `r>0`, every inclusion

```text
F=H_0 > H_1 > ... > H_n                                   (8)
```

is strict.

## Proof

### Embedding rigidity

Let `sigma:F -> U` fix `H_n(Y)` and put `h=sigma(y)-y`. Since `sigma` fixes `delta^n y`,

```text
delta^n h=0.                                               (9)
```

Therefore `h` is differentially algebraic over `C`. The field `C<y,h>` contains `C<y>`, whose
differential transcendence degree over `C` is `d`, while adjoining the differentially algebraic
tuple `h` cannot increase that degree. Hence

```text
dtrdeg(C<y,h>/C<h>)=d.                                    (10)
```

If `y` satisfied an extra ordinary algebraic equation over `C<h>`, then its ordinary
transcendence degree over `C<h>` would be less than `d`, forcing the differential transcendence
degree in `(10)` to be less than `d`. Thus `y` remains an algebraic generic point of `Y` over
`C<h>`.

For every `P in I(Y)`, the tuple `sigma(y)=y+h` lies in `Y`, so

```text
P(y+h)=0.                                                  (11)
```

Because `y` is generic on `Y` over `C<h>`, equation `(11)` says that translation by `h` maps
`Y_(C<h>)` into itself. Its image is an irreducible closed subvariety of the same dimension, so
the inclusion is equality. Therefore `h in Stab_trans(Y)(C<h>)=A(C<h>)`. Together with `(9)` this
proves `(3)`.

Conversely, translation by an `h in A intersection K_n` preserves every algebraic equation of
`Y` and preserves `delta^n y`; when `y` is generic over `C<h>`, substitution gives the stated
field embedding.

### Fixed-field separation and reconstruction

Quantifier elimination for `DCF_0` implies that the definable closure of a differential field is
the field itself. Consequently

```text
H_n(Y) = {f in F : sigma(f)=f for every H_n(Y)-embedding F -> U}.   (12)
```

If `A=0`, equation `(3)` makes every such embedding the identity, so `(12)` yields `F=H_n(Y)`.
If `A` is nonzero, any nonzero `c in A(C)` gives a nontrivial translation automorphism
`y |-> y+c` that fixes `delta^n y`; hence `H_n(Y)` is proper. This proves `(4)`.

### Splitting and the torsor tower

Choose `A^m=A direct_sum B`. If `(a,b) in Y`, translation by `-a in A` shows `(0,b) in Y`; the
reverse translation recovers the full fiber. Therefore `Y=A x (Y intersection B)` on algebraic
points, hence as reduced affine varieties. Any translation stabilizing `Z=Y intersection B`
would lift to a translation of `Y`, so `Z` has trivial stabilizer. This proves `(5)` and `(6)`.

Finally, `H_j` is generated over `H_(j+1)` by the vector `delta^j a`, which solves the first-order
inhomogeneous system in `(7)`. The corresponding unipotent fundamental matrix is

```text
[ I_r   delta^j a ]
[  0         1     ],
```

so the extension is Picard--Vessiot with additive group `G_a^r`. Constant translations make each
layer strict when `r>0`.

## Why the original automorphism claim was false

For `Y=A^1` and a differential indeterminate `x`,

```text
H_n=C<delta^n x>.
```

At `n>1`, the ordinary automorphisms of `C<x>/H_n` do not realize all of `ker(delta^n)` inside
`C<x>`. The information loss is instead resolved by the chain

```text
C<x> > C<delta x> > ... > C<delta^n x>,
```

one additive Picard--Vessiot torsor at a time. Replacing an ordinary fixed-field claim by the
embedding groupoid `(3)` and the tower `(7)` is essential, not terminological.

## New geometric and physical content

The result is a no-hair theorem for derivative horizons:

```text
finite-depth horizon hair = maximal affine-cylinder dimension.    (13)
```

The defect is independent of horizon depth and insensitive to all nonlinear reduced geometry.
Depth changes only the length of the unipotent integration tower.

Physically, `ker(delta^n)` is a finite clock-jet gauge: changing the first `n` integration data
does not change the observed tail. The algebraic constraint acts like an exact Higgs mechanism.
Every nonlinear direction fixes its clock jet; only flat additive directions retain gauge. This
does not turn the HT source into a flow. It describes the static equivalence relation induced by
forgetting finite jets.

The quotient `Y -> Y/A=Z` is the precise topology behind the horizon: leaves are affine spaces,
the leaf space is translation-rigid, and the horizon reconstructs the leaf-space coordinate at
every depth.

## Parent-theory and novelty gate

- Picard--Vessiot torsors and Kolchin's use of embeddings into a universal differential field are
  classical.
- Quantifier elimination and definable closure for `DCF_0` are classical.
- Constant affine-group differential invariants and jet/arc invariant theory are classical.
- The rational-curve theorem in the source card is a special case.
- No checked source states the combined arbitrary-variety classification `(3)--(8)`, the
  depth-independent criterion `(4)`, or the exact cylinder/torsor interpretation `(6)--(8)`.

The novelty label remains conservative until specialist and literature review. The theorem is not
claimed to be Fields-Medal scale merely because it closes the stated proof wall.

## Lean formalisation boundary

The exact first non-affine case is formalised in
`formal/GaloisForLFunctions/HTGeometry/NonlinearConstraintHorizon.lean`:

```text
z=x*y,
W=x' y''-x'' y' != 0
```

implies that every derivation-closed field containing `x'`, `y'`, and `z'` contains both `x` and
`y`. Lean verifies the explicit reconstruction identities and the intermediate-field theorem with
no axioms or placeholders. The general DCF embedding-groupoid theorem is not encoded as an
assumption.

## RH impact audit

`[FORMULATION TOOL; NOT RH PROGRESS]` Any multichannel source-pure model for completed zeta data
would now have to exhibit an actual affine-cylinder factor to support finite-jet information loss.
A nonlinear observation constraint with trivial translation stabilizer cannot hide an RH-relevant
branch behind any finite derivative horizon. No canonical affine observation variety for the zeta
field has been identified, so the result presently yields no zero-location claim.

## Gates

- [x] 0 -> 1 in-progress: gauge quotient conjecture and exact proof wall identified
- [x] 1 -> 2 fully-proven: embedding rigidity, DCF separation, cylinder splitting, and torsor
  tower proved; incorrect ordinary-automorphism formulation removed
- [x] 2 -> 3 formalized: `(3)`-`(9)` all unconditional in Lean; the DCF layer was replaced by the
  Taylor arc, the transcendence crux and the algebraic primitive descent
- [ ] 3 -> 4 publication-ready: external differential-algebra specialist and exhaustive
  literature audit

## References

- D. Marker, *Model Theory: An Introduction*, Chapter 4 and Section 7.4; differential closure,
  quantifier elimination, and differential Galois groups.
- P. J. Cassidy and M. F. Singer, *Galois theory of parameterized differential equations and
  linear differential algebraic groups*, for differential algebraic Galois groups.
- G. R. Maurischat, *Picard--Vessiot theory of differentially simple rings*, for the torsor
  formulation of Picard--Vessiot extensions.
- S. Bekbaev, *On rational differential invariants of the field of rational functions in several
  indeterminates under an action of a subgroup of the affine group*, for the affine-invariant
  parent theory.

## Log

- 2026-07-15 — conjectured that the horizon was an ordinary fixed field of `A(K_n)`.
- 2026-07-15 — affine-line falsification at depth `n>1` forced the embedding-groupoid correction.
- 2026-07-15 — proved embedding rigidity, the all-depth reconstruction criterion, exact cylinder
  splitting, and the successive additive-torsor law.

## Lean progress — the cylinder splitting `(5)` and the horizon gauge `(3)`, `(9)`

`GaloisForLFunctions.HTGeometry.JetHorizonTranslationGauge` formalizes the two structural halves of
the theorem, unconditionally and axiom-clean (`[propext, Classical.choice, Quot.sound]`).  Neither
needs the differentially closed field, so neither is blocked on the missing DCF layer.

**The canonical cylinder decomposition `(5)`.**  For an arbitrary subset `Y` of an abelian group,
the translation stabilizer is a subgroup and splits `Y` against any complement of it:

```text
transStab Y = {a | ∀ y, y + a ∈ Y ↔ y ∈ Y}          an AddSubgroup
mem_iff_exists_add_slice   IsCompl (transStab Y) B  ==>
    y ∈ Y  ↔  ∃ a ∈ transStab Y, ∃ z ∈ Y ∩ B, y = a + z
add_slice_unique           the decomposition is unique
transStab_slice_eq_bot     transStab (Y ∩ B) = ⊥   whenever the slice is nonempty
```

so `Y = A × Z` with `Stab_trans(Z) = 0`, which is `(5)` at the level of points and groups.  The
proof of the rigidity of the slice is the card's: a translation preserving `Z` lies in `B` because
`Z ⊆ B` is nonempty, and it preserves `Y` because `Y` is `A + Z`; hence it lies in `A ⊓ B = 0`.

**The horizon gauge `(3)`, `(9)`.**  For a derivation `δ` and a map `σ` commuting with it:

```text
pow_comp_apply                 σ commutes with every iterate of δ
pow_apply_sub_eq_zero          σ (δ^n y) = δ^n y  ==>  δ^n (σ y − y) = 0
mem_ker_pow_of_fix             the displacement lies in ker (δ^n)
pow_apply_add_of_apply_eq_zero δ c = 0  and  n ≥ 1  ==>  δ^n (y + c) = δ^n y
```

The first pair is `(9)` — the displacement of a depth-`n` horizon embedding is annihilated by `δ^n`
— and the last is the converse half used in `(4)`: a nonzero constant in the stabilizer translates
the generic point without moving its depth-`n` jet, so `H_n(Y)` is proper whenever `A ≠ 0`.

What remains, and is exactly the card's stated boundary: the DCF inputs — differential genericity,
`dtrdeg` invariance under adjoining a differentially algebraic tuple, and quantifier elimination
giving `(12)` — together with the Picard--Vessiot identification of the layers `(7)`.

## Lean progress — the depth-independent horizon gauge, with no model theory

The DCF layer named as this card's boundary is avoidable.  Six new modules replace the embedding
groupoid `(3)` and the rigid half of `(4)` by differential algebra, unconditionally and
axiom-clean.

**The Taylor arc.**  `GaloisForLFunctions.HTGeometry.DifferentialTaylorMorphism` builds

```text
differentialTaylor : R → R⟦T⟧,   a ↦ Σ_n (δ^n a / n!) T^n
```

for a differential ℚ-algebra, and proves it is a ring homomorphism, is injective, satisfies
`d/dT ∘ τ = τ ∘ δ`, sends constants to constants, sends a polynomial expression to that polynomial
evaluated on the arcs, and identifies `ker δ^n` with the arcs supported in degrees below `n`.  The
jets of a point *are* a formal arc on its locus; this is what removes the need for a differentially
closed ambient field.

**Translation rigidity.**  `AffineTranslationStabilizerRigidity` proves that a translation carrying
an affine locus into itself carries it onto itself: translation induces a surjective endomorphism of
the coordinate ring, and a surjective endomorphism of a Noetherian ring is injective
(`injective_of_surjective_endomorphism_of_isNoetherianRing`, proved from the kernel chain).  Point
form: `aeval_add_eq_zero_iff`.

**The infinitesimal criterion.**  `AffineConstantVectorFieldTranslation` realizes translation by a
constant vector as the exponential of the constant vector field `Σ h i ∂/∂X i`: the parametrized
translation `P ↦ P(X + T h)` is exactly the Taylor morphism of the polynomial ring for that vector
field, so its `k`-th coefficient is `(1/k!) D_h^k P` and its value at `T = 1` is the translation.
Hence an ideal stable under `D_h` is stable under translation by `h`.

**The gauge.**  `JetHorizonFirstDepthRigidity` proves the chain rule `D (P(z)) = (D_h P)(z)` for a
derivation moving the coordinates by constants `h`, deduces that `h` is tangent to the locus, and
concludes `IsTranslationSymmetry z h` — the constant displacement is a translation symmetry of the
locus.  Both the infinitesimal form (derivations) and the finite form (differential embeddings) are
proved.

**Depth independence.**  `JetHorizonAllDepthGauge` proves that in a differential field with no
primitive of one, `ker δ^n` is exactly the constants — a tower of primitives collapses one floor at
a time — so the displacement of a horizon of *any* positive depth is already constant and the
depth-one analysis applies verbatim:

```text
derivation_apply_eq_zero_of_translationRigid_depth
    δ-commuting derivation killing δ^n z, translation-rigid locus  ==>  D z = 0
apply_eq_self_of_translationRigid_depth
    δ-commuting endomorphism fixing δ^n z, translation-rigid locus  ==>  σ z = z
```

This is the card's `(3)` together with the rigid half of `(4)`, at every depth, and it explains the
affine-line counterexample of the "Why the original automorphism claim was false" section: there
`δ x = 1`, so the field *does* have a primitive of one and the collapse fails.  The hypothesis is
sharp — for `δ x = 1` and `z = (x, x²)` the locus is translation rigid while `H_2 = C`.

**The canonical generic setting.**  `JetFieldNoPrimitiveOfOne` proves the free differential
rational field has no primitive of one (differentiation raises jet order), and specializes both
rigidity statements to points of `JetField C ι`.

Still open, and now the exact boundary: the *existence* half — that a nontrivial translation
stabilizer really produces a nontrivial horizon gauge — and the transcendence-degree count
`trdeg(C⟨y⟩ / C⟨δ^n y⟩) = n · dim A` with the torsor tower `(7)`, `(8)`.  Both need the differential
ideal of a differential-generic point to be generated by the algebraic ideal of its locus, which is
the remaining genericity layer.

## Lean progress — the reconstruction criterion `(4)`, both directions

The remaining half of `(4)` — that a translation-rigid locus really *is* reconstructed — is now
proved as well, and it needs neither quantifier elimination nor differential genericity.

**The transcendence crux.**  `GaloisForLFunctions.HTGeometry.DifferentialTranscendenceCrux`: let
`K ⊆ F` be a derivation-closed intermediate field, let `F` be generated over `K` by a family whose
derivatives all lie in `K`, and suppose some member of the family is transcendental over `K`.  Then
`F` carries a **nonzero derivation over the constants which kills `K` and commutes with the
derivation**.  The construction is a transcendence basis chosen *inside the generating family*
(`exists_isTranscendenceBasis_subset`), constant prescribed values on it
(`DerivationPrescription.exists_derivation_prescribed`), and the observation that the commutator
`⁅δ, D⁆` kills `K` — because `K` is derivation closed — and kills every basis element — because the
derivative of a generator lies in `K` while the prescribed value is a constant — hence vanishes,
since `F` is algebraic over `K(basis)`.

**Algebraic primitives descend.**  `DifferentialPrimitiveDescent.mem_of_isAlgebraic_of_deriv_mem`:
an element algebraic over a derivation-closed intermediate field whose derivative lies in that
field lies in the field itself, when the extension has no new constants.  Differentiating the
minimal polynomial gives a relation of strictly smaller degree, which must vanish; its
second-highest coefficient exhibits the element, corrected by that coefficient over the degree, as
a constant.

**The criterion.**  `JetHorizonReconstruction`:

```text
differentialAdjoin_deriv_eq_top_of_gaugeTrivial
    every δ-commuting derivation killing δz kills z  ==>  C⟨δz⟩ = C⟨z⟩
differentialAdjoin_deriv_eq_top_of_translationRigid
    translation-rigid locus                          ==>  C⟨δz⟩ = C⟨z⟩
differentialAdjoin_differentialJet_eq_top_of_translationRigid
    translation-rigid locus, no primitive of one     ==>  C⟨δ^n z⟩ = C⟨z⟩ for every n
```

The depth induction is the one the card's tower predicts: once `F = C⟨δ^j z⟩`, the pair
`(C⟨δ^{j+1} z⟩, F)` is again a depth-one situation for the point `δ^j z`, and the collapse
`ker δ^n = C` of `JetHorizonAllDepthGauge` shows that a `δ`-commuting derivation killing
`δ^{j+1} z` already kills `δ^j z`, which the crux forbids unless the extension is algebraic.  The
primitive descent then upgrades "algebraic" to "equal".

Together with `DifferentialGenericPointHorizon`, which supplies the converse for a differentially
generic point and arbitrary `Y`, this is `(4)` in both directions.  What remains of the card is the
Picard--Vessiot identification of the successive layers `(7)`; the strictness `(8)` follows from the
converse half, and the cylinder bookkeeping `(6)` from `JetHorizonCylinderDecomposition`.

## Lean progress — the successive-torsor law `(7)`

`GaloisForLFunctions.HTGeometry.JetHorizonTorsorTower` supplies the structure of a single layer:

```text
jetHorizon C y j                              the depth-`j` horizon
deriv_differentialJet_mem_jetHorizon_succ     each adjoined jet solves δ X = δ^{j+1} y in the
                                              next horizon
jetHorizon_succ_le                            the horizons decrease with depth
mem_differentialAdjoin_iff_mem_adjoin         a differential field generated by a family whose
                                              derivatives lie in a derivation-closed subfield is
                                              that subfield with the family adjoined
mem_jetHorizon_iff_mem_adjoin_succ            hence H_j is H_{j+1} with the depth-`j` jets adjoined
```

So each step of the tower is generated over the next by solutions of the inhomogeneous additive
equation `δ X = δ^{j+1} y` with coefficient in the lower layer — the equation whose additive
Picard--Vessiot torsor the card names.  `JetHorizonAdditiveLayer` bounds the gauge group of such a
layer inside the additive group of constants, and `JetHorizonCylinderGauge` realizes the whole of
that group in the pure-cylinder case; `DifferentialGenericPointHorizon` gives the strictness `(8)`.
What is still missing from `(7)` is only the realization of every constant as a layer automorphism
over a *non-constant* base.

## Lean progress — the successive-torsor law `(7)` is closed; the card is formalized

`GaloisForLFunctions.HTGeometry.JetHorizonAdditiveTorsorLaw` supplies the last missing half:
every constant vector is realized by a layer automorphism, over a base that need not be constant,
and in the rank the card requires.

```text
differentialConstants F                     the constant subfield of a differential field
vectorDerivativeField F q                   F<q'> for a family q, the lower layer
vectorDerivativeField_adjoin_eq_top         T is F<q'> with the family q adjoined ordinarily
vectorDerivativeAlgEquiv_ext                a layer automorphism is determined by its values on q
exists_vectorTranslationEquiv               translation of a free differential family by a vector
                                            of base scalars is a differential automorphism
vectorTranslationEquiv_fixes_vectorDerivativeField
                                            translation by a vector of *constants* fixes the whole
                                            lower layer pointwise
vectorConstTranslationAction                the resulting action of the constant vector group
vectorConstTranslationAction_injective      it is faithful
vectorConstTranslationAction_surjective     every derivation-preserving automorphism of the layer
                                            is such a translation
vectorAdditiveGaloisGroupEquiv              hence Aut_delta(T / F<q'>) = (constants of F)^iota
coe_differentialConstants_eq_range          constants do not grow along a constant-sharing base
vectorAdditiveGaloisGroupEquivConstantField Aut_delta(T / F<q'>) = G_a^iota(C)
```

Two hypotheses of the existing `ScalarAdditiveDifferentialTorsor` had to go.  That module computes
the same group for a single coordinate under `hconst : forall c : F, c' = 0`, i.e. for a base field
consisting entirely of constants; the layers of a jet horizon sit over `C<z>`, the reduced part of
the generic point, which carries a nonzero derivation.  The observation that removes the hypothesis
is that only constancy of the *translating scalar* is ever used: `sigma (q_i)' = (q_i + c_i)' =
(q_i)'` needs `c_i' = 0` and nothing else, and the surjectivity direction produces a constant of
`F` rather than an arbitrary element because `sigma q_i - q_i` is a constant of `T` and `T` shares
its constants with `F`.  The rank was raised from one to an arbitrary index type at the same time,
since `DifferentialIndependent`, `DifferentialIndependent.addBase`,
`differentialAdjoin_addOfJetsInBase` and `differentialIndependentTopAlgEquiv` are all already
indexed by an arbitrary family.

Taking `F = C<z>`, `q = delta^j a` and `T = H_j`, the hypotheses read: the cylinder coordinates are
differentially independent over the reduced part, they generate the layer, and no new constants
appear.  The conclusion is exactly `(7)`: the layer `H_j / H_(j+1)` is the additive torsor of
`delta X = delta^(j+1) a` with differential Galois group `G_a^r`, `r = dim A`.

**The card is now fully formalized.**  Every numbered assertion is unconditional Lean with axioms
`[propext, Classical.choice, Quot.sound]`:

| Card | Lean |
|---|---|
| `(3)` embedding rigidity | `JetHorizonFirstDepthRigidity.isTranslationSymmetry_of_derivation`, `JetHorizonAllDepthGauge.apply_eq_self_of_translationRigid_depth`, `DifferentialGenericPointHorizon.translationSymmetry_eq_zero_of_mem_differentialAdjoin` |
| `(4)` reconstruction criterion, both directions | `JetHorizonReconstruction.differentialAdjoin_differentialJet_eq_top_of_translationRigid` and `DifferentialGenericPointHorizon.differentialAdjoin_differentialJet_ne_top_of_translationSymmetry` |
| `(5)` cylinder splitting | `JetHorizonTranslationGauge.mem_iff_exists_add_slice`, `add_slice_unique`, `transStab_slice_eq_bot` |
| `(6)` depth bookkeeping | `JetHorizonCylinderDecomposition.differentialAdjoin_union_differentialJet_eq` |
| `(7)` successive-torsor law | `JetHorizonTorsorTower.mem_jetHorizon_iff_mem_adjoin_succ`, `JetHorizonAdditiveLayer.injective_displacement`, `JetHorizonAdditiveTorsorLaw.vectorAdditiveGaloisGroupEquivConstantField` |
| `(8)` strictness | `JetHorizonCylinderGauge.differentialAdjoin_differentialJet_ne_top_of_free`, `DifferentialGenericPointHorizon.differentialAdjoin_differentialJet_ne_top_of_translationSymmetry` |
| `(9)` displacement lies in `ker delta^n` | `JetHorizonTranslationGauge.mem_ker_pow_of_fix` |

The DCF layer named as the card's formalisation boundary was never needed.  The Taylor arc
`tau(a) = sum delta^n(a)/n! T^n` of `DifferentialTaylorMorphism` replaces the embedding into a
differentially closed field: the jet sequence of a point *is* a formal arc on its locus, so
translation invariance of the locus is a statement about polynomial identities in a formal power
series ring rather than a model-theoretic one.  Quantifier elimination is replaced by the
transcendence crux of `DifferentialTranscendenceCrux` together with the algebraic primitive descent
of `DifferentialPrimitiveDescent`.
