# The field with one element

## Status, scope, and answer

There is no ordinary field with one element. There is also no single accepted
replacement whose carrier, addition, modules, spectra, scalar extension, and
points agree with every construction called `F₁`.

The mathematically stable answer is a **loss-aware doctrine atlas**:

1. a common multiplicative core

   `F₁^mult = {0,1}`;

2. several inequivalent enhancements that retain different extra structure;
3. explicit forgetful, quotient, and base-extension maps between those
   enhancements;
4. a named point functor whenever points are counted.

This document develops that answer. It does not use `F₁` as a route to the
Riemann hypothesis and does not assume conjectural cohomology, positivity, or
an absolute Frobenius.

Claim labels:

- `[FORMALIZED]`: unconditional Lean theorem in this repository;
- `[PAPER-PROVED]`: dependency-closed proof recorded in research pipeline;
- `[LITERATURE]`: theorem or construction from cited source;
- `[INTERPRETATION]`: synthesis, not theorem;
- `[NO-GO]`: stronger reading proved false;
- `[OPEN]`: not established.

## 1. Why a literal one-element field is impossible

An ordinary field is a nontrivial commutative ring. Nontriviality means
`0≠1`, so its carrier contains at least two elements. The one-element ring is
the zero ring, where `0=1`; it is not a field.

The phrase “field with one element” therefore names a change of algebraic
doctrine, not a missing entry in the list of finite fields.

The target behavior is instead:

- one multiplicative unit;
- one absorbing basepoint;
- no chosen total addition;
- free modules behaving like pointed finite sets;
- `GL_n` degenerating to the symmetric group;
- scalar extension to ordinary rings recovering familiar algebraic geometry.

Those requirements lead to the multiplicative core.

## 2. The common multiplicative core

### 2.1 Definition

Let `CMon₀` be the category of commutative monoids equipped with an absorbing
zero. Morphisms preserve zero, one, and multiplication.

Define

`F₁^mult = {0,1}`

with `0·x=0` and `1·x=x`.

In Lean this is

`WithZero PUnit`.

### 2.2 Universal property

`[FORMALIZED]` For every `A∈CMon₀`, exactly one morphism

`F₁^mult → A`

exists: it must send `0` to `0_A` and `1` to `1_A`.
Thus `F₁^mult` is initial in `CMon₀`.

Every nonzero element of `F₁^mult` is invertible, since the only nonzero
element is `1`. This is the exact field-like property available without
addition.

Lean certificate:

- `FieldOneCore.FieldOne`
- `FieldOneCore.fieldOne_hom_unique`
- `FieldOneCore.fieldOne_eq_zero_or_one`
- `FieldOneCore.fieldOne_isUnit_of_ne_zero`

in
[`formal/GaloisForLFunctions/HTGeometry/FieldOneMultiplicativeCore.lean`](../formal/GaloisForLFunctions/HTGeometry/FieldOneMultiplicativeCore.lean).

### 2.3 Contracted scalar extension

For a commutative semiring `R` and a pointed monoid `A`, ordinary monoid
algebra retains a basis vector `[0_A]`. That vector is an unwanted idempotent.
Correct scalar extension is the **contracted monoid algebra**

`R[A]^c = R[A]/([0_A])`.

For `F₁^mult`, only `[1]` remains, so

`R[F₁^mult]^c ≃ R`.

This is valid for every commutative semiring, hence for every commutative
ring. In particular,

`Z[F₁^mult]^c ≃ Z`.

`[NO-GO]` Replacing contracted algebra by ordinary monoid algebra is wrong:
ordinary `R[{0,1}]` retains the absorbing-zero basis vector and is not the
desired base change.

Lean certificate:

- `FieldOneCore.ContractedBaseChange`
- `FieldOneCore.contractedBaseChangeEquiv`

### 2.4 Modules and linear algebra

An `F₁^mult`-module is a pointed set `(M,0_M)`. Its action is forced:

`0·m=0_M`,
`1·m=m`.

Every pointed set admits this action. A function between two such modules is
equivariant exactly when it preserves the basepoint.

The free module on a set `I` is

`I₊ = I ⊔ {0}`.

Restriction to generators gives

`Hom_*(I₊,M) ≃ (I→M)`.

Every pointed automorphism fixes the added zero and permutes `I`; conversely,
every permutation extends by fixing zero. Therefore

`Aut_F₁(I₊) ≃ Perm(I)`.

For `I=Fin n`,

`GL_n(F₁) ≃ S_n`.

This is the precise Tits linear-algebra identity. No limiting computation in
`q` is needed.

Lean certificate:

- `FieldOneCore.fieldOneMulActionWithZero`
- `FieldOneCore.ZeroHom.map_fieldOne_smul`
- `FieldOneCore.zero_preserving_of_fieldOne_equivariant`
- `FieldOneCore.freeFieldOneModuleHomEquiv`
- `FieldOneCore.freeFieldOneModuleAutMulEquiv`

### 2.5 Module/Tits projective points

The unit group of `F₁^mult` is trivial. Quotienting nonzero vectors of `I₊`
by scalar units therefore does nothing. The module/Tits point set is
canonically `I`.

For `I=Fin n`, this convention gives

`#P^(n−1)(F₁) = n`.

Lean certificate:

- `FieldOneCore.nonzeroFreeFieldOneModuleEquiv`
- `FieldOneCore.card_projectiveModulePoints`

This count is not the full point set of monoid-Proj; section 4 separates the
two functors.

## 3. Total addition cannot be doctrine-neutral

Suppose a nontrivial semiring has carrier `{0,1}`. Then `1+1` must be one of
the two carrier elements:

`1+1=0` or `1+1=1`.

The alternatives are disjoint.

- If `1+1=0`, every element satisfies `x+x=0`. This is the
  characteristic-two branch represented by `F₂`.
- If `1+1=1`, every element satisfies `x+x=x`. This is the Boolean,
  idempotent branch represented by `B`.

`[FORMALIZED]` These two branches exhaust every total semiring addition on a
nontrivial two-element carrier.

Lean certificate:

- `FieldOneCore.twoElement_additiveFork`
- `FieldOneCore.twoElement_additiveFork_disjoint`

`[NO-GO]` Multiplication on `{0,1}` does not select a canonical total
addition. Calling either `F₂` or the Boolean semifield “the” field with one
element silently chooses an enhancement.

Blueprints, ordered blueprints, bands, hyperrings, and pastures escape the
fork by using partial, multivalued, or relational addition rather than a
third total operation.

## 4. Affine and projective monoid geometry

### 4.1 Free affine coordinates

For a set of variables `I`, let

`E_I = N^(I)`

be finitely supported exponent vectors. Define

`F₁[T_i | i∈I] = {0} ∪ {T^e | e∈E_I}`,

with

`T^e T^f = T^(e+f)`.

This is the free commutative monoid with zero on `I`.

Its contracted scalar extension is

`R[F₁[T_i]]^c ≃ R[T_i | i∈I]`.

`[FORMALIZED]` The equivalence holds for every commutative semiring `R`.

Lean certificate:

- `FieldOneCore.AffineCoordinateMonoid`
- `FieldOneCore.affineContractedBaseChangeEquiv`

in
[`formal/GaloisForLFunctions/HTGeometry/FieldOneAffineGeometry.lean`](../formal/GaloisForLFunctions/HTGeometry/FieldOneAffineGeometry.lean).

### 4.2 Prime monoid ideals

A monoid ideal contains zero and is closed under multiplication by arbitrary
elements. It is prime when it is proper and

`ab∈P ⇒ a∈P or b∈P`.

For `S⊆I`, define

`P_S={0} ∪ {T^e | supp(e)∩S≠∅}`.

Every `P_S` is prime. Conversely, every prime ideal is some `P_S`: take

`S_P={i | T_i∈P}`.

Factorization of a monomial into variable powers and repeated primality give

`T^e∈P ↔ supp(e)∩S_P≠∅`.

Hence

`Spec F₁[T_i] ≃ Set(I)`

as point sets. Inclusion satisfies

`P_S⊆P_T ↔ S⊆T`,

so the specialization poset is the Boolean lattice of coordinate subsets.

For `I=Fin n`,

`#A^n_F₁ = 2^n`

for the underlying monoid-spectrum point functor.

`[FORMALIZED]` Lean proves the ideal classification, equivalence, and count:

- `FieldOneCore.coordinatePrime_isPrime`
- `FieldOneCore.prime_eq_coordinatePrime`
- `FieldOneCore.coordinatePrime_subset_iff`
- `FieldOneCore.coordinatePrimeEquiv`
- `FieldOneCore.card_affineMonoidSpectrum`

### 4.3 Projective monoid-spectrum points

Give every variable degree one. The irrelevant ideal is generated by every
`T_i`. Under the subset classification, it is `P_I`.

Monoid-Proj removes that prime. Its points correspond to proper subsets of
`I`, equivalently nonempty complements. For `I=Fin n`,

`#|P^(n−1)_F₁|_monoid-Proj = 2^n−1`.

`[FORMALIZED]`

- `FieldOneCore.ProjectiveMonoidPoint`
- `FieldOneCore.card_projectiveMonoidSpectrum`

The two valid projective counts are therefore:

| Point functor | `P^(n−1)(F₁)` |
|---|---:|
| module/Tits rational points | `n` |
| underlying monoid-Proj points | `2^n−1` |

`[NO-GO]` “The points of projective space over `F₁`” is incomplete unless
the point functor is named.

## 5. Signed relational addition: `F₁±`

### 5.1 Bands

For a pointed monoid `B`, let `B⁺` be the semiring of finite formal sums of
nonzero elements of `B`. A **band** equips `B` with a null ideal
`N_B⊆B⁺` such that every `a∈B` has a unique `−a` satisfying

`a+(−a)∈N_B`.

The current band base is

`F₁±={0,1,−1}`.

Its nonzero multiplication is `C₂`, and its null set consists of balanced
formal sums

`n·1+n·(−1)`.

`[LITERATURE]` `F₁±` is initial in bands and in idylls. The Krasner
hyperfield `K={0,1}` is terminal in idylls, not initial; its null set contains
every sum with at least two copies of `1`. See
[Baker–Jin–Lorscheid](https://arxiv.org/abs/2402.09612).

### 5.2 Formalized signed core

`[FORMALIZED]` Balanced sums contain zero, are closed under addition, remain
balanced under multiplication by every sign, and give every sign a unique
additive inverse.

Lean certificate:

- `FieldOneCore.SignedNull`
- `FieldOneCore.signedNull_add`
- `FieldOneCore.signedNull_scalar`
- `FieldOneCore.signed_additiveInverse_unique`

in
[`formal/GaloisForLFunctions/HTGeometry/FieldOneSignedAxis.lean`](../formal/GaloisForLFunctions/HTGeometry/FieldOneSignedAxis.lean).

### 5.3 Carrier separation

The multiplicative core has carrier `{0,1}`. The initial band has carrier
`{0,1,−1}`.

`[FORMALIZED]`

- there is a multiplicative collapse `−1↦1`;
- no zero-and-one preserving injection exists in the opposite direction;
- no type can be equivalent to both carriers.

Lean certificate:

- `FieldOneCore.signedCollapse`
- `FieldOneCore.no_signed_embedding_into_fieldOne`
- `FieldOneCore.no_signed_equiv_fieldOne`
- `FieldOneCore.no_literal_common_carrier`

This proves the smallest decisive no-go:

`[NO-GO]` A literal one-carrier theory cannot simultaneously be the initial
pointed monoid and the initial band.

### 5.4 Forgetting null relations changes scalar extension

Forget the balanced null relation. The signed nonzero group is `C₂`, so
multiplicative contracted base extension is

`R[C₂] ≃ R[u]/(u²−1)`.

Retain the band relation `1+u=0`. It specializes `u` to `−1`:

`R[u]/(u²−1,u+1) ≃ R[u]/(u+1) ≃ R`.

`[FORMALIZED]` Evaluation at `u=−1` gives the final equivalence and sends the
signed generator to `−1`.

Lean certificate:

- `FieldOneCore.SignedMultiplicativeBaseChange`
- `FieldOneCore.SignedBandBaseChange`
- `FieldOneCore.signedBandBaseChangeEquiv`
- `FieldOneCore.signedBandGenerator_specializes`

Thus a forgetful map must record lost scalar-extension relations. Carrier
forgetting is not harmless.

## 6. Group-like and cyclotomic extensions

Let `G` be an abelian group. Adjoining an absorbing zero gives

`G₀={0}⊔G`.

Every nonzero element is invertible, and the unit group of `G₀` is canonically
`G`. Conversely, every commutative group with zero is canonically zero
adjoined to its unit group:

`K ≃ WithZero(Kˣ)`.

`[FORMALIZED]` This classifies every group-like extension of the
multiplicative core.

Lean certificate:

- `FieldOneCore.FieldOneGroupExtension`
- `FieldOneCore.groupExtensionUnitsEquiv`
- `FieldOneCore.commGroupWithZeroClassification`
- `FieldOneCore.groupExtension_isUnit_of_ne_zero`

in
[`formal/GaloisForLFunctions/HTGeometry/FieldOneCyclotomicExtensions.lean`](../formal/GaloisForLFunctions/HTGeometry/FieldOneCyclotomicExtensions.lean).

Contracted scalar extension is the group algebra:

`R[G₀]^c=R[G]`.

For the cyclic group `C_n`, define

`F_(1^n)={0}⊔C_n`.

It has `n` units and one absorbing zero, hence `n+1` carrier elements, and

`R[F_(1^n)]^c=R[C_n]`.

`[FORMALIZED]`

- `FieldOneCore.CyclotomicFieldOne`
- `FieldOneCore.card_cyclotomicFieldOne`
- `FieldOneCore.CyclotomicBaseChange`

The notation `F_(1^n)` is mnemonic, not literal cardinal arithmetic. For
`n=1` it recovers `F₁^mult`. For `n=2` its pointed-monoid carrier is
`{0,1,−1}`; adding balanced null sums upgrades that carrier to `F₁±`.

## 7. Doctrine atlas

No row below is declared the winner. Each solves a different extension
problem.

| Doctrine | Base object or base idea | Algebra retained | Classical realization | What it explains | Exact boundary |
|---|---|---|---|---|---|
| Pointed monoids / Deitmar | `{0,1}` | multiplication, zero | contracted monoid algebra | toric geometry, free modules, `GL_n=S_n` | addition absent; finite-type image is restrictive |
| Toën–Vaquié relative schemes | tensor unit of `(Set,×,*)` | commutative monoid objects in a symmetric monoidal category | change of base category | conceptual relative geometry | depends on chosen ambient monoidal category |
| Soulé gadgets | functorial gadget plus complex algebra | point data and evaluation | scalar extension to `Z` | early `F₁` varieties, toric examples, zeta functions | not a single algebraic carrier |
| Blueprints | monoid plus pre-addition relations | multiplication and selected additive congruences | associated semiring/ring | common home for monoids, semirings, rings, Chevalley/Tits models | several spectrum and ideal notions remain |
| Ordered blueprints | ordered additive relations | order, bend relations, multiplication | tropicalization/base extension | tropical and analytic geometry | order is extra structure, not core data |
| Bands / idylls | `F₁±` initial; Krasner terminal among idylls | multiplication plus null sums and unique weak negatives | impose null relations in ring algebra | matroids, partial fields, hyperfields, Tits horizons | carrier differs from `{0,1}`; module scheme theories need care |
| Hyperrings / pastures | often Krasner or tropical hyperfield | multivalued addition | realization through bands/tracts or hyperrings | matroid foundations, valuations | not equivalent to every band-scheme construction |
| Idempotent semirings | Boolean `B`, tropical `Z_max`, `R_max` | total idempotent addition and order | semiring schemes/dequantization | tropical geometry and characteristic one | chooses Boolean branch `1+1=1` |
| `F₂` branch | two-element field | total ring addition | already an ordinary finite field | characteristic-two algebra | is `F₂`, not addition-free `F₁` |
| Borger `Λ`-geometry | `Λ`-rings as descent data | commuting Frobenius lifts | forget `Λ`-structure to rings | arithmetic descent and Frobenius organization | base is a descent doctrine, not a smaller carrier |
| Durov generalized rings | commutative algebraic monads; initial generalized ring | finitary operations encoded monadically | generalized schemes and Arakelov models | `F₁`, `Z_∞`, tropical objects, intersection/Chern formalism | large categorical apparatus; comparisons are partial |
| Haran non-additive geometry | `F`-rings / finite pointed-set operations | multi-input/multi-output non-additive operations | embedding of rings | compactification and products over an absolute base | distinct from Durov, blue, and monoid categories |
| Sphere / brave-new algebra | sphere spectrum as initial `E_∞` ring | coherent homotopy operations | `S→HZ` | stable-homotopy and algebraic `K`-theory intuition | derived, not discrete; `π₀(S)=Z`, not a one-element carrier |
| Segal `Γ`-sets and `S`-algebras | identity `Γ`-set / sphere `S` | coherent operations at every finite pointed set | Eilenberg–Mac Lane functor for rings/semirings | envelope for monoids, semirings, hyperrings, monads | higher levels contain data invisible at `1₊` |
| Congruence spaces | congruences rather than only prime ideals | quotient-sensitive topology | comparison to monoid schemes | valuative criteria and topological refinement | point set differs from prime spectrum |
| Arithmetic / Scaling Site | `Z_max` sheaf over arithmetic topos; scalar extension toward `R_max` | idempotent semiring sheaves and Frobenius correspondences | tropical/adelic realization | arithmetic dynamics and characteristic-one curves | analytic-topos enhancement, not algebraic core |

### 7.1 Proven categorical relationships

- `[LITERATURE]` Deitmar monoid schemes and Toën–Vaquié schemes over sets
  agree in the relevant affine/scheme setting:
  [Vezzani](https://arxiv.org/abs/1005.0287).
- `[LITERATURE]` Blueprints contain commutative monoids and commutative
  semirings/rings as full subcategories and supply a common scheme theory:
  [Lorscheid, Part I](https://arxiv.org/abs/1103.1745).
- `[LITERATURE]` Segal `Γ`-algebra provides a functorial envelope for several
  monoid, semiring, hyperring, and monadic constructions:
  [Connes–Consani](https://arxiv.org/abs/1502.05585).
- `[LITERATURE]` Current `Γ`-ring work takes spectrum topology from the
  level-`1₊` pointed monoid and uses all `Γ`-levels for localization and the
  structure sheaf:
  [Xu, July 2026](https://arxiv.org/abs/2607.04843).

### 7.2 Proven incompatibilities

- `[FORMALIZED]` Initial pointed-monoid and initial-band carriers cannot be
  literally identical.
- `[FORMALIZED]` Total addition on the two-element carrier has two
  incompatible branches.
- `[FORMALIZED]` forgetting band null relations changes base extension.
- `[LITERATURE]` Latest band-module work proves the module category is closed
  symmetric monoidal, complete, cocomplete, and proto-exact, while finding
  incompatibility between relative band schemes and affine hyperring scheme
  theories:
  [Hamada, May 2026](https://arxiv.org/abs/2606.01093).

These are reasons for an atlas, not defects to conceal.

## 8. The loss-aware atlas construction

### 8.1 Nodes

An atlas node records:

1. algebraic doctrine;
2. base object;
3. category of algebras or modules;
4. spectrum or geometric realization;
5. scalar-extension functor;
6. chosen point functors;
7. unconditional theorems available in that doctrine.

Minimum nodes:

- `M`: multiplicative pointed-monoid core `F₁^mult`;
- `A₂`: total characteristic-two enhancement `F₂`;
- `AB`: total Boolean enhancement `B`;
- `R`: relational-addition enhancement through blueprints/bands;
- `D`: Frobenius-descent enhancement through `Λ`-rings;
- `G`: generalized-operation enhancement through monads or Haran `F`-rings;
- `S`: spectral/coherent enhancement through sphere or `Γ`-algebras;
- `T`: ordered/tropical enhancement;
- `An`: arithmetic/analytic topos enhancement.

### 8.2 Edges

Every atlas edge must declare its kind:

- **forgetful**: discards structure;
- **quotient**: imposes relations;
- **base extension**: changes coefficients/doctrine;
- **realization**: sends algebra to geometry;
- **comparison**: equivalence, fully faithful embedding, adjunction, or only a
  natural transformation.

Every non-equivalence edge carries a loss ledger:

- carrier identifications;
- additive or null relations forgotten/imposed;
- change in module category;
- change in scalar extension;
- change in spectrum;
- change in point functor;
- change in exactness or homotopy data.

Example:

`F₁± --forget null sums--> signed pointed monoid`

changes scalar extension from `R` to `R[C₂]`.

Example:

`F₁± --collapse signs--> K`

identifies `−1` with `1` and requires a larger target null set.

### 8.3 Coherence requirements

A proposed comparison is accepted only when it specifies commuting maps for:

1. base object;
2. free algebra;
3. scalar extension;
4. localization;
5. spectrum;
6. modules;
7. selected point functors.

Agreement on carriers alone is insufficient. Agreement after base extension
alone is also insufficient.

### 8.4 Universal claim retained

`[PAPER-PROVED]` The doctrine-independent universal claim is narrow:

> `{0,1}` is the initial commutative monoid with zero, its contracted scalar
> extension is the coefficient semiring, and its modules are pointed sets.

No stronger universal carrier claim survives the signed-band and additive-fork
audits.

### 8.5 Formal atlas certificate

`[FORMALIZED]` The atlas construction itself is machine-checked:

- `FieldOneDoctrine` indexes all doctrine families in section 7;
- `DoctrineProfile` requires every node to have a nonempty enhancement-axis
  profile and records named point functors;
- `CertifiedProjectivePointFunctor` pairs each proved projective point carrier
  with its exact count;
- `LossAwareAtlasEdge` requires a nonempty loss ledger for every
  non-equivalence;
- `signedForgetfulEdge`, `signCollapseEdge`, and
  `monoidRelativeEquivalenceEdge` are the initial evidence-labelled edges;
- `AtlasEvidence` separates formalized, literature, and mixed evidence;
- `ComparisonFacet` makes the seven coherence checks in section 8.3 an
  exhaustive finite checklist;
- `doctrineAtlas_no_literal_common_carrier` proves that the atlas cannot be
  replaced by one carrier;
- the total-addition nodes and the two certified projective point functors
  remain distinct.

Lean certificate:

- `FieldOneCore.primaryAxis_mem_doctrineProfile`
- `FieldOneCore.certifiedProjectivePointCount_correct`
- `FieldOneCore.nonEquivalence_has_named_loss`
- `FieldOneCore.every_comparisonFacet_required`
- `FieldOneCore.fieldOneDoctrineAtlas`
- `FieldOneCore.doctrineAtlas_no_literal_common_carrier`
- `FieldOneCore.moduleTits_ne_monoidProj`
- `FieldOneCore.characteristicTwo_ne_idempotent`

in
[`formal/GaloisForLFunctions/HTGeometry/FieldOneDoctrineAtlas.lean`](../formal/GaloisForLFunctions/HTGeometry/FieldOneDoctrineAtlas.lean).

This organizational certificate does not pretend that naming a doctrine
formalizes its entire published scheme theory. Exact mathematical claims are
certified in their doctrine modules or retained as cited literature. The
atlas is the formal object that keeps those claims indexed without identifying
incompatible structures.

## 9. Current frontier through 26 July 2026

### 9.1 Stable results

- Deitmar monoid geometry remains the smallest algebraic core.
- Toën–Vaquié supplies the relative-category formulation.
- Blueprints and ordered blueprints bridge monoid, semiring, ring, and
  tropical constructions.
- Bands provide a current relational-addition foundation with an initial
  signed base and strong matroid applications.
- Congruence spaces add quotient-sensitive topology and valuative criteria:
  [Lorscheid–Ray](https://arxiv.org/abs/2305.12801).
- `Γ`-algebras supply the broadest current coherent-operation envelope.

### 9.2 2025–2026 changes that matter

1. **Initial carrier changed by doctrine.** The 2025 band theory has
   `F₁±={0,1,−1}` initial in bands and idylls, while Krasner `{0,1}` is
   terminal among idylls. “Every approach uses `{0,1}`” is false.
2. **Band modules are now structurally robust.** May 2026 work establishes
   closed symmetric monoidal, complete, cocomplete, and proto-exact module
   structure.
3. **Compatibility is not automatic.** The same work reports incompatibility
   with affine hyperring scheme theories.
4. **Absolute affine `Γ`-geometry now has localization and spectrum.** The
   July 2026 preprint constructs localization, structure sheaves, and affine
   anti-equivalence; it uses the level-`1₊` pointed monoid for topology.

`[INTERPRETATION]` These results strengthen the atlas model: multiplicative
topology can be shared while additive/coherent sheaf data remain doctrine
specific.

## 10. Iterative conjecture ledger

### C1. One carrier subsumes every construction

- Initial status: `[CONJECTURE]`
- Attack: compare initial objects in pointed monoids and bands.
- Result: `[FALSE]`
- Killing theorem: carriers have two and three elements; no literal common
  carrier exists.
- Positive survivor: doctrine atlas with explicit comparison maps.

### C2. Addition can be restored canonically on `{0,1}`

- Initial status: `[CONJECTURE]`
- Attack: classify `1+1`.
- Result: `[FALSE]`
- Killing theorem: exactly characteristic-two and Boolean branches exist.
- Positive survivor: relational or partial addition is a separate axis.

### C3. Forgetting enhancement data preserves base extension

- Initial status: `[CONJECTURE]`
- Attack: forget the null relation in `F₁±`.
- Result: `[FALSE]`
- Killing theorem: multiplicative base extension is `R[C₂]`; band base
  extension is `R`.
- Positive survivor: every atlas edge needs a loss ledger.

### C4. There is one projective point count

- Initial status: `[CONJECTURE]`
- Attack: compare module/Tits points with monoid-Proj primes.
- Result: `[FALSE]`
- Killing theorem: counts are `n` and `2^n−1`.
- Positive survivor: point functor is part of the construction.

### C5. A common multiplicative core is still meaningful

- Initial status: `[CONJECTURE]`
- Attack: initiality, scalar extension, module category, free automorphisms,
  affine coordinates, and prime spectra.
- Result: `[PAPER-PROVED] [FORMALIZED]`
- Scope: pointed-monoid core and multiplicative shadows only.

## 11. Formalization inventory

| Theorem package | Paper card | Lean module | Status |
|---|---|---|---|
| initial multiplicative core, contracted base change, pointed modules, `GL_I` | `field-one-multiplicative-core.md` | `FieldOneMultiplicativeCore.lean` | `[FORMALIZED]` |
| exhaustive total-addition fork | `field-one-additive-fork.md` | `FieldOneMultiplicativeCore.lean` | `[FORMALIZED]` |
| free affine coordinates, polynomial base change, prime classification, affine/projective counts | `field-one-affine-projective-monoid-geometry.md` | `FieldOneAffineGeometry.lean` | `[FORMALIZED]` |
| signed null sums, carrier no-go, multiplicative collapse, band specialization | `field-one-signed-band-axis.md` | `FieldOneSignedAxis.lean` | `[FORMALIZED]` |
| group-with-zero classification and `F_(1^n)` extensions | `field-one-group-cyclotomic-extensions.md` | `FieldOneCyclotomicExtensions.lean` | `[FORMALIZED]` |
| doctrine index, node profiles, named projective counts, evidence-labelled loss-aware edges, coherence checklist, atlas no-go | `field-one-loss-aware-doctrine-atlas.md` | `FieldOneDoctrineAtlas.lean` | `[FORMALIZED]` |

All Lean theorems are unconditional. No `sorry`, `admit`, local axiom,
`opaque`, or `unsafe` declaration is used.

## 12. What “the field with one element” means after construction

Use the following terminology:

- **`F₁^mult`**: the exact two-element initial pointed monoid.
- **`F₁±`**: the exact three-element initial band/idyll.
- **`B`**: Boolean total-addition enhancement.
- **`K`**: Krasner hyperfield, terminal idyll.
- **`S`**: sphere/identity `Γ`-object in spectral or absolute algebra.
- **`F₁` without a superscript**: the entire doctrine atlas, with node named
  locally whenever a theorem depends on one.

This convention prevents four common category errors:

1. treating `F₁` as an ordinary field;
2. identifying `{0,1}`, `F₂`, and `B`;
3. identifying `{0,1}` with `F₁±`;
4. conflating rational, topological, congruence, tropical, and geometric
   points.

## 13. Completion boundary and external comparison frontier

The field-one construction developed here is complete at its stated
method-neutral interface: multiplicative base, modules, affine and projective
monoid geometry, total-addition fork, signed relational base, group-like
extensions, doctrine index, loss-aware edges, point-functor separation, and
comparison requirements are paper-proved and formalized.

Completeness does not mean declaring unequivalent published theories
equivalent. Following pairwise comparison problems remain external research
frontier and can add certified atlas edges without changing the construction:

- exact comparison of blueprint, ordered-blueprint, band, pasture, and
  hyperring spectra beyond known embeddings;
- formal comparison between band modules and `Γ`-algebra modules;
- exact relation between Borger `Λ`-descent and `Γ`-ring Witt constructions;
- comparison of Durov and Haran generalized rings at the level of schemes,
  localization, and products;
- compatibility of congruence spaces with band and `Γ` spectra;
- richer machine-checked realizations of each doctrine behind its indexed
  node.

These are doctrine-realization and comparison problems, not missing axioms of
the field-one construction and not a request for an RH proof.

## Primary sources

- Anton Deitmar,
  [*Schemes over F₁*](https://arxiv.org/abs/math/0404185).
- Bertrand Toën and Michel Vaquié,
  [*Au-dessous de Spec Z*](https://arxiv.org/abs/math/0509684).
- Alberto Vezzani,
  [*Deitmar’s versus Toën–Vaquié’s schemes over F₁*](https://arxiv.org/abs/1005.0287).
- Christophe Soulé,
  [*Les variétés sur le corps à un élément*](https://arxiv.org/abs/math/0304444).
- Oliver Lorscheid,
  [*The geometry of blueprints, Part I*](https://arxiv.org/abs/1103.1745).
- Oliver Lorscheid,
  [*F₁ for everyone*](https://arxiv.org/abs/1801.05337).
- Oliver Lorscheid,
  [*Ordered blueprints and tropicalization*](https://arxiv.org/abs/1508.07949).
- Matthew Baker, Tong Jin, and Oliver Lorscheid,
  [*New building blocks for F₁-geometry: bands and band schemes*](https://arxiv.org/abs/2402.09612).
- Lucas Hamada,
  [*On the category of modules over bands*](https://arxiv.org/abs/2606.01093).
- Oliver Lorscheid and Samarpita Ray,
  [*The topological shadow of F₁-geometry: congruence spaces*](https://arxiv.org/abs/2305.12801).
- James Borger,
  [*Λ-rings and the field with one element*](https://arxiv.org/abs/0906.3146).
- Nikolai Durov,
  [*New Approach to Arakelov Geometry*](https://hdl.handle.net/20.500.11811/3110).
- Shai Haran,
  [*Non-additive geometry*](https://cage.ugent.be/~kthas/Fun/library/ShaiHaran2007.pdf).
- Alain Connes and Caterina Consani,
  [*Absolute algebra and Segal’s Gamma sets*](https://arxiv.org/abs/1502.05585).
- Alain Connes and Caterina Consani,
  [*The Arithmetic Site*](https://arxiv.org/abs/1405.4527).
- Alain Connes and Caterina Consani,
  [*Geometry of the Scaling Site*](https://arxiv.org/abs/1603.03191).
- Luqiao Xu,
  [*Localization and Affine Schemes over F₁*](https://arxiv.org/abs/2607.04843).
