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

Sections 1--13 develop that answer unconditionally. Sections 14--19 then audit
every major `F₁`-to-RH route against one common gate system and isolate exact
remaining construction. They do not assume conjectural cohomology, positivity,
an absolute Frobenius, or RH. As of 26 July 2026, field-one construction is
formalized; RH route is not complete.

Claim labels:

- `[FORMALIZED]`: unconditional Lean theorem in this repository;
- `[PAPER-PROVED]`: dependency-closed proof recorded in research pipeline;
- `[LITERATURE]`: theorem or construction from cited source;
- `[INTERPRETATION]`: synthesis, not theorem;
- `[NO-GO]`: stronger reading proved false;
- `[FALSIFIED]`: a conjectured implication has been killed;
- `[CONJECTURE]`: precise claim under active hostile audit;
- `[OPEN CORE]`: exact missing theorem;
- `[BRIDGE]`: proved implication or equivalence, not proof of its premise;
- `[LEAN-PROVED]`: unconditional theorem checked in Lean;
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
the field-one construction.

## 14. Absolute arithmetic geometry and RH-facing constructions

The phrase `F₁` has two different roles which must not be conflated:

1. the algebraic doctrine atlas constructed in Sections 1--13;
2. an absolute arithmetic geometry intended to place
   \(\overline{\operatorname{Spec}\mathbb Z}\) in a curve-like theory.

The first is complete at its stated interface. The second is where an RH route
could live. Base, spectrum, or point-count constructions alone cannot supply
the faithful global positivity required by RH.

### 14.1 The 2026 absolute arithmetic curve

`[LITERATURE]` Connes--Consani construct
\[
  X_{\mathrm{abs}}
  =
  (\operatorname{Spec}\mathbb Z)_{\mathbb F_1}
\]
by pulling the arithmetic-site \(\mathbb F_1\)-structure sheaf back to
\(\operatorname{Spec}\mathbb Z\). At a prime \(p\), the stalk is partially
perfected:
\[
  \mathbb F_1[T^{\mathbb Z[1/p]_+}],
\]
and \(p\)-power Frobenius becomes invertible. This is the spherical/`Γ` node
of doctrine atlas, not bare `F₁^mult`; comparison must preserve that
enhancement. Perfectoid-valued points recover untilt geometry;
complex-valued points give local Weil torsors.
The archimedean quotient at \(p\) is a complex Tate curve
\[
  E_p\simeq C_p\times\widetilde X_\infty,\qquad
  C_p=\mathbb R_+^\times/p^\mathbb Z.
\]
Thus one factor has arithmetic length \(\log p\), while the phase circle is
\(p\)-independent.

`[NO-GO]` This is a geometric carrier, not an RH proof. The paper constructs no
middle arithmetic cohomology, positive Hodge form, Hodge-index theorem, or
purity theorem. Moreover, radial time \(\log p\) is the identity on the whole
local Tate curve, so the local tangent return is degenerate. A Tate curve is a
prime boundary packet; it is not automatically Deninger's isolated closed
orbit.

### 14.2 Arithmetic Picard/Jacobian monoids

`[LITERATURE]` Connes--Consani also construct arithmetic Picard and Jacobian
monoids, their extended Abel--Jacobi map, and adelic covers. The Riemann sector
becomes a monoidal moduli space of torsion-free rank-one groups with metric
data. Its closed fibers carry prime orbits; its generic fiber carries the
regular representation.

Their semilocal trace formula has form
\[
  \operatorname{Tr}(\theta(h)R_\lambda)
  =
  2h(1)\log\lambda
  +
  \sum_{v\in S}
    \int_{\mathbb Q_v^\times}^{\prime}
      \frac{h(u^{-1})}{|1-u|}\,d^\ast u
  +o(1).
\]
The divergent first term is interpreted as generic-point “white light.” This
suggests the relative pair
\[
  \left(
    \widetilde{\operatorname{Pic}}
      (\overline{\operatorname{Spec}\mathbb Z}),
    \widetilde\eta
  \right).
\]

`[INTERPRETATION]` This changes the frontier materially. Absolute carrier and
geometric support of local explicit-formula terms are concrete. Missing object
is a faithful relative cohomology with positive, flow-natural Hodge form.

`[NO-GO]` Removing a divergent generic summand does not make the remainder
positive. Mapping cones encode relative information; they do not have an
automatic Hodge-index theorem. The Picard/Jacobian paper states neither
positivity nor RH.

### 14.3 Cuntz--Krieger `F₁` geometry

`[LITERATURE]` Nikolaev's 2026 Cuntz--Krieger construction assigns matrices and
\(C^\ast\)-algebras to projective `F₁` varieties. It obtains a trace point-count,
rational zeta function, functional equation, and degree formula.

`[NO-GO]` The paper explicitly excludes the RH analogue from its proved Weil
properties. Rationality and functional equation constrain reciprocal symmetry,
not eigenvalue modulus. Its final Conjecture 4.3 asserts an equivalence between
classical RH and an `F₁` elliptic-curve RH statement, but supplies no comparison
from the finite rational zeta function to the infinite Xi divisor. Its
construction is therefore an independent atlas lane, not a missing proof of
purity.

### 14.4 What the latest affine work adds

`[LITERATURE]` Xu's 2026 `Γ`-algebra theory supplies localization, prime
spectrum, structure sheaf, global-section recovery, and affine
anti-equivalence. It strengthens the absolute affine node in the doctrine
atlas. It contains no arithmetic middle cohomology or RH theorem.

## 15. Method-neutral RH gate atlas

Every route is judged by the same gates. No route receives credit for a gate
proved only in another doctrine unless a comparison theorem transports the
relevant structure without loss.

| Gate | Required content |
|---|---|
| G0: source purity | objects defined from primes, Gamma factor, `F₁` geometry, or arithmetic correspondences before reading Xi zeros |
| G1: arithmetic carrier | global object over \(\overline{\operatorname{Spec}\mathbb Z}\), not only a finite-field analogy or local factor |
| G2: local-to-global trace | exact prime-power and archimedean terms with controlled generic contribution |
| G3: middle cohomology | infinite-dimensional degree one, with closed Frobenius/flow generator |
| G4: duality | cup product, trace, Poincaré duality, and correct odd/quaternionic parity |
| G5: faithful positivity | positive Hodge/intersection form detecting finite and density-zero defects |
| G6: comparison | source trace/determinant equals completed zeta/Xi data without assuming zero location |
| G7: purity extraction | flow-natural Hodge form, Hodge index, or equivalent source passivity forcing critical-line spectrum |

Current lane audit:

| Lane | Established input | Exact missing gate |
|---|---|---|
| monoid, blueprint, band, tropical, `Γ` geometry | bases, spectra, modules, scalar extensions, point functors | G1--G7 for arithmetic Xi |
| Borger `Λ`/Witt descent | commuting Frobenius lifts and descent philosophy | archimedean completion, G3--G7 |
| sphere-spectrum/spectral algebra | coherent absolute operations and stable-homotopy carrier | zeta-level completion rather than only logarithmic/additive invariants; G3--G7 |
| arithmetic/scaling site | prime orbits, Frobenius correspondences, Riemann--Roch strategy | intersection/Hodge-index theorem on square; G5 and G7 |
| absolute curve and Picard pair | G1, geometric local support, generic-point interpretation | relative cohomology, faithful Hodge norm, G5--G7 |
| rational-Witt/Milnor--Witt Deninger program | source complexes, finite transfers, duality algebra, local quaternionic half-density, determinant and RH consumers | global dynamical lift plus positive flow-natural Hodge realization |
| adelic/Sonin/passivity | semilocal trace operators, source resolvents, exact RH-equivalent source criteria | faithful global continued passivity |
| Cuntz--Krieger | rationality, functional equation, cohomological degree data for projective `F₁` zeta | RH/purity analogue explicitly open |
| \(q\to1\) Weil-II analogy | Deligne purity for each actual finite field | a genuine arithmetic family through \(q=1\), compatible cohomology, and positivity at its limit |

The lanes are complementary but not interchangeable. Algebraic `F₁` doctrines
organize carriers and descent; arithmetic-site and adelic geometry organize
orbits and traces; Deninger and Weil criteria identify the required sign. Any
lane may close RH only by supplying all missing gates or an exact structure-
preserving comparison to a lane which does.

## 16. Exact formal RH endpoints already available

The repository has formalized consumers. It has not formalized their missing
geometric premises.

### 16.1 Continued two-pole source passivity

Let
\[
  T(z)=\text{continued prime--archimedean relative trace}
\]
be built from the meromorphically continued prime carrier and Gamma/boundary
factor. Define
\[
  K(z,w)=
  \frac{T(\overline w)-T(z)}{z-\overline w}
\]
and, for two admissible separated poles,
\[
  \mathcal E(z,w;a,b)
  =
  |a|^2K(z,z)+a\overline bK(z,w)
  +b\overline aK(w,z)+|b|^2K(w,w).
\]

`[BRIDGE] [LEAN-PROVED]`
`riemannHypothesis_iff_ccmContinuedTwoPoleSourcePassivity` proves
\[
  \mathrm{RH}
  \quad\Longleftrightarrow\quad
  \operatorname{Re}\mathcal E(z,w;a,b)\ge0
\]
for every admissible \(z,w,a,b\). The reverse direction uses an unequal-speed
two-pole approximation to the negative sign direction of any off-line zero.
Consequently the rank-two family is already faithful; enlarging the test space
does not remove the open core.

This is not an RH proof because source passivity is not proved.

### 16.2 Deninger Hodge naturality

The Deninger stack already constructs a source-defined entire quotient,
arithmetic trace and Poincaré interfaces, local positive quaternionic Hodge
atoms, finite transfer laws, and several exact RH consumers.

`[BRIDGE] [LEAN-PROVED]`
`deningerDivisorClosedTheta_orientedHodge_iff_riemannHypothesis` identifies the
remaining purity condition: the positive odd Hodge/Riesz factor must commute
with centered Frobenius after source-to-divisor comparison.

This is not an RH proof because global source construction and flow naturality
remain open. It is a second exact endpoint, not a preferred method.

### 16.3 Positive source atoms are not the missing theorem

`[LEAN-PROVED]`
`DeningerArithmeticRectangularQuaternionicHodge.lean` constructs local
moving-rectangle Hodge atoms \(J_r\), proves \(J_r^2=-1\), strict positive
energy, energy preservation, and centered half-density covariance without Xi
data.

`[LEAN-PROVED]` `DeningerArithmeticGammaRankRegular.lean` constructs
\[
  J_0(a,b)=(-\overline b,\overline a)
\]
on \(\ell^2(G\sqcup G)\), with \(J_0^2=-1\), antiunitarity, and norm
preservation from a dense source core.

These results close local positivity and coefficient-level quaternionic
parity. They do not prove that relative arithmetic relations form a closed
\(J_0\)-stable subspace, that induced quotient is faithful, or that its norm is
continued prime--archimedean energy. Global descent and exact comparison remain
RH-bearing gates.

## 17. RH iterative conjecture ledger

### C6. One absolute Frobenius collapses arithmetic complexity and forces RH

- Initial status: `[CONJECTURE]`
- Attack: compare single-Frobenius corank with prime-log and Stieltjes carriers.
- Result: `[FALSIFIED]`
- Killing mechanism: one Frobenius can collapse algebraic/transcendence
  bookkeeping while leaving zero location untouched.
- Positive survivor: distinguish linear `F₁` collapse from algebraic `F₁`
  collapse and from analytic purity.

### C7. RH is the formal derivative at \(q=1\) of finite-field purity

- Initial status: `[CONJECTURE]`
- Attack: require a differentiable arithmetic family of fields, cohomologies,
  Frobenii, pairings, and comparison maps through \(q=1\).
- Result: `[FALSIFIED AS A PRESENT PROOF]`
- Killing mechanism: prime powers are discrete, and no such family with
  compatible purity is constructed. Declaring its tangent is the missing
  `F₁` geometry in different words.
- Positive survivor: any valid \(q\to1\) route must first construct the family
  and prove specialization preserves faithful positivity.

### C8. Positive local traces glue to RH

- Initial status: `[CONJECTURE]`
- Attack: compare normalized/measured traces with finite and density-zero
  off-line defects.
- Result: `[FALSIFIED]`
- Killing mechanism: measured index and normalized trace can assign zero to
  sparse defects. Local positivity also does not control a signed global
  renormalization.
- Positive survivor: transition maps must be isometric and global completion
  faithful, not only trace-preserving.

### C9. Relative generic-point excision is automatically positive

- Initial status: `[CONJECTURE]`
- Attack: model relative cohomology as a mapping cone.
- Result: `[FALSIFIED AS A FORMAL IMPLICATION]`
- Killing mechanism: a cone subtracts generic contribution but can retain an
  indefinite finite part.
- Positive survivor: the relative Picard pair is canonical support for a
  Hodge construction whose positivity must be proved separately.

### C10. A Gram realization of the continued kernel is the missing geometry

- Initial status: `[CONJECTURE]`
- Attack: apply positive-kernel reconstruction in reverse.
- Result: `[FALSIFIED AS CIRCULAR]`
- Killing mechanism: existence of Hilbert vectors
  \(b_z\) with \(K(z,w)=\langle b_z,b_w\rangle\) is positive definiteness of
  \(K\), already equivalent to RH.
- Positive survivor: vectors and norm must be explicitly constructed from
  local `F₁`/Picard source data before kernel equality is proved.

### C11. Put the semilocal source sheaf on finite Picard truncations

- Initial status: `[CONJECTURE]`
- Attack: type every space, sheaf, restriction, and derived section functor.
- Result: `[FALSIFIED AS ILL-TYPED]`
- Killing mechanism: crossed-product sheaf is constructed on
  \(\operatorname{Spec}\mathbb Z\), while proposed
  \(\widetilde{\operatorname{Pic}}_S\) and its coefficient sheaf were not
  defined.
- Positive survivor: extend source sheaf across archimedean place and
  derive-push it along Abel--Jacobi before forming relative Picard cohomology.

### C12. Push directly from compactified curve and excise one Picard point

- Initial status: `[CONJECTURE]`
- Attack: compare proposed map and generic object with primary-source
  universal-cover diagram.
- Result: `[FALSIFIED AS WRONG SOURCE MAP]`
- Killing mechanism: trace support uses universal Abel--Jacobi embedding
  \(\widetilde{\operatorname{Spec}\mathbb Z}\hookrightarrow
  \widetilde{\operatorname{Pic}}\). Generic regular representation is a
  stratum/fiber, not justified as one point.
- Positive survivor: pull coefficients to universal adelic cover, push along
  universal embedding, and excise full generic stratum.

### C13. A single Cuntz--Krieger `F₁` elliptic RH is equivalent to RH

- Initial status: `[LITERATURE] [CONJECTURE]`
- Attack: require an exact comparison between two RH statements.
- Result: `[OPEN; NOT A PROOF]`
- Obstruction: constructed `F₁` zeta is finite-degree rational, while completed
  Riemann zeta has an infinite nontrivial divisor. No cofinal limit,
  determinant identity, or faithful spectral comparison is supplied.
- Positive survivor: Cuntz--Krieger lane gives concrete Frobenius matrices and
  order structure. A viable successor must build an infinite arithmetic
  system whose regularized determinant is completed zeta and whose positive
  cone controls every spectral direction.

### C14. Universal-cover relative Picard Hodge passivity

- Status: `[CONJECTURE] [OPEN CORE]`
- Active card:
  `docs/drafts/pipeline/1-in-progress/field-one-relative-picard-hodge-passivity.md`.
- Claim: compare spherical, compactified, and analytic coefficient sheaves;
  extend source sheaf to compactified curve; pull it to universal adelic
  cover; derive-push along universal Abel--Jacobi embedding; excise complete
  generic stratum; and construct source two-pole classes with a faithful odd
  Hodge norm equal to
  \(\operatorname{Re}\mathcal E\).
- Current verdict: survives second type audit; construction and proof remain
  open.

This conjecture does not replace parallel Deninger, scaling-site, Sonin, or
operator-algebra lanes. It gives the newest absolute/Picard lane a typed target
and a shared formal endpoint.

### C15. Ordinary scalar extension supplies the spherical-to-arithmetic bridge

- Initial status: `[CONJECTURE]`
- Attack: at a prime \(p\), compare ordinary integral base change of
  \(\mathbb F_1[T^M]\), namely \(\mathbb Z[M]\), with
  \(\mathbb Z[1/p]\).
- Result: `[FALSIFIED] [PAPER-PROVED] [LEAN-PROVED]`
- Killing mechanism: augmentation
  \(\mathbb Z[M]\to\mathbb Z\) proves scalar \(p\ge2\) remains a nonunit in
  every \(\mathbb Z[M]\), while localization makes \(p\) a unit. Hence no
  \(\mathbb Z\)-algebra equivalence exists, for any additive monoid \(M\).
- Exact positive survivor: augmentation followed by localization gives a
  canonical comparison
  \[
    \mathbb Z[M]\longrightarrow\mathbb Z[1/p],
  \]
  but sends every monomial \(T^m\) to \(1\), and is noninjective whenever
  \(M\) has two distinct elements. Thus its complete loss ledger is formal:
  it discards exponent and Frobenius-monomial data.
- Lean certificate:
  `GaloisForLFunctions.HTGeometry.FieldOneSphericalLocalizationNoGo`.

C14 survives this audit only as a zigzag of typed, doctrine-specific
comparisons. Any branch needing prime Frobenius or exponent data may not factor
solely through the augmentation--localization edge.

### C16. Spherical monomials are semilocal analytic coefficients

- Initial status: `[CONJECTURE]`
- Attack: send \(T^h\) to the additive character
  \(x\mapsto\alpha_S(hx)\) in
  \(\mathcal S(\mathbb A_S)\).
- Result: `[FALSIFIED AS ILL-TYPED]`
- Killing mechanism: a nonzero additive character has unit modulus and full
  support, so it is not Bruhat--Schwartz on noncompact \(\mathbb A_S\).
- Positive survivor: it is a continuous unitary **multiplier** of
  \(\mathcal S(\mathbb A_S)\).

`[PAPER-PROVED]` For every finite \(S\ni\{\infty,p\}\), multiplication by
\[
  \chi_h(x)=\alpha_S(hx),\qquad h\in\mathbb Z[1/p],
\]
gives a faithful representation \(h\mapsto W_h\) on semilocal
Bruhat--Schwartz space. It satisfies
\[
  W_{h+k}=W_hW_k,\qquad
  W_{h/p}^{\,p}=W_h,\qquad
  \theta(u)W_h\theta(u)^{-1}=W_{u^{-1}h},
\]
and is unitary on \(L^2(\mathbb A_S)\). Thus it retains spherical exponent,
\(p\)-perfection, and scaling data without ordinary scalar extension.

This closes RP0 at each fixed semilocal stage. Compatibility with all sheaf
restriction maps, compactified extension, and derived Picard transport remain
open. Paper card:
`docs/drafts/pipeline/2-fully-proven/field-one-spherical-weyl-multiplier-bridge.md`.

`[LEAN-PROVED]` Algebraic character/root/faithfulness laws are in
`FieldOneWeylCharacterBridge.lean`. Archimedean temperate growth, continuous
Schwartz multiplication, inverse law, root law, and faithfulness are in
`FieldOneArchimedeanWeylMultiplier.lean`. Existing
`L2MellinUnitary.lean` independently supplies unitary Fourier-phase
multiplication on \(L^2(\mathbb R)\).
`FieldOneLocallyConstantWeylMultiplier.lean` proves finite-place
compact-support/local-constancy preservation, inverse and root laws, and
scaling covariance for every locally constant additive character.
`FieldOnePadicWeylCharacter.lean` constructs, for every prime \(p\), a
nontrivial locally constant character of \(\mathbb Q_p\) trivial on
\(\mathbb Z_p\), normalized nontrivially on \(p^{-1}\), and instantiates the
finite-place multiplier. Its extension beyond the depth-one cyclic subgroup
is noncanonical. `FieldOnePadicStandardWeylCharacter.lean` replaces that
existence proof with the canonical compatible system on
\(p^{-n}\mathbb Z_p\): it proves exact normalization at every \(p^{-n}\),
kernel exactly \(\mathbb Z_p\), local constancy, nontriviality, and the Weyl
composition law. `FieldOneFiniteAdeleWeylCharacter.lean` then assembles these
local characters by finite support over the restricted product, proving a
canonical nontrivial locally constant character of \(\mathbb A_f\) and its
Weyl composition law. `FieldOneFiniteAdeleDiagonalReciprocity.lean` proves
directly that on every fixed-prime exponent lattice
\(\mathbb Z[1/p]\), the finite character equals \(q\bmod\mathbb Z\) on
diagonal \(q\), and therefore cancels the negative archimedean character.
`FieldOneRationalPrimaryReciprocity.lean` factors an arbitrary reduced
denominator into pairwise-coprime prime powers, constructs Bézout
coefficients, and upgrades this to
\(\psi_f(\Delta_f q)=q\bmod\mathbb Z\) for every \(q\in\mathbb Q\).
`FieldOneSemilocalBruhatWeylTensor.lean` forms the algebraic carrier
\[
  \mathcal S(\mathbb R)\otimes_{\mathbb C}
    C_c^{\mathrm{lc}}(\mathbb A_f),
\]
assembles the \(2\pi\)-normalized real and finite multipliers, and proves
the pure-tensor, additive, identity, inverse, automorphism, and rational
diagonal laws. `FieldOneFiniteAdeleIntegralBruhatTest.lean` proves
\(\prod_v\mathbb Z_v\) compact open, constructs its nonzero characteristic
Bruhat vector, and contracts the finite tensor factor by evaluation at zero.
`FieldOneSemilocalArchimedeanFaithfulness.lean` uses that contraction to prove
that semilocal operator equality forces equality of archimedean coordinates;
in particular, the rational diagonal action is faithful.
`UnitModulusL2Multiplier.lean` proves the measure-independent theorem that
every measurable unit-modulus phase acts unitarily on complex \(L^2\).
`FieldOneFiniteAdeleL2WeylMultiplier.lean` derives finite-adele local
compactness from the compact-open integral subgroup, installs Borel Haar
measure, proves finite-adele \(L^2\) unitarity, embeds Bruhat tests into
\(L^2\), and proves exact compatibility of the algebraic and \(L^2\)
multipliers. `FieldOneSemilocalL2WeylMultiplier.lean` proves the corresponding
unitary action on product-Haar
\(L^2(\mathbb R\times\mathbb A_f)\), including additive and rational diagonal
laws. `FieldOneFiniteAdeleSelfDuality.lean` proves the standard finite
character primitive and the finite Bruhat Weyl action faithful.
`FieldOneSemilocalFullFaithfulness.lean` adds archimedean-zero contraction
against the Gaussian and proves the full
\(\mathbb R\times\mathbb A_f\) algebraic Weyl action faithful.
`FieldOneSemilocalBruhatToL2.lean` sends every algebraic pure tensor to its
pointwise product in product-Haar \(L^2\), descends this construction
bilinearly to the full algebraic tensor, and proves exact equivariance with
the algebraic and \(L^2\) Weyl actions. Its square-integrability proof avoids
an unavailable finite-adele sigma-finiteness premise.
`FunctionTensorProduct.lean` proves algebraically that finite sums of
separated scalar functions have unique tensor coefficients.
`FieldOneSemilocalBruhatL2Embedding.lean` orients product measure with the
known sigma-finite real factor on `Measure.prod`'s required side, transports
by coordinate swap, proves open positivity, and combines continuous
representatives with function-tensor uniqueness to prove the
Schwartz--Bruhat-to-\(L^2\) map injective.
`FieldOneSemilocalBruhatHilbertCompletion.lean` pulls back the ambient
\(L^2\) norm and inner product, identifies the resulting abstract Hilbert
completion isometrically with the closure of the algebraic image, extends
every algebraic Weyl automorphism to a unitary, and proves exact completed
intertwining and the additive action law. This is a completed comparison to
the generated closed subspace, not a proof that the subspace is all product
\(L^2\). Full-product density and sheaf-restriction compatibility remain
open.

## 18. Step-by-step non-circular construction target

Let
\[
  \mathscr A_{\mathrm{src}}(S^c)
  =
  \mathcal S(\mathbb A_S)\rtimes\mathbb Z_S^\times
\]
be the source sheaf already constructed on
\(\operatorname{Spec}\mathbb Z\), with \(S\ni\infty\) recording the semilocal
archimedean factor. Let \(X=\overline{\operatorname{Spec}\mathbb Z}\), let
\[
  \pi:\widetilde X\longrightarrow X,\qquad
  \widetilde\Theta:
  \widetilde X\hookrightarrow
  \widetilde{\operatorname{Pic}}
    (\overline{\operatorname{Spec}\mathbb Z})
\]
be universal adelic cover and universal Abel--Jacobi embedding. Following
steps are required. All derived operations must be
\(C_{\mathbb Q}\)-equivariant so scaling flow and its generator survive.

1. **Doctrine comparison.** Construct explicit comparison zigzags among
   spherical absolute sheaf
   \(\mathcal F=\Theta^{-1}\mathbb F_1[T]\), completed
   Eilenberg--MacLane/unit-ball sheaf \(\mathcal O_X\), and analytic
   \(\mathscr A_{\mathrm{src}}\). Prove preservation and loss ledger for prime
   Frobenius, products, archimedean boundary, and \(C_{\mathbb Q}\)-action.
   Ordinary integral scalar extension is already ruled out as an equivalence:
   the canonical augmentation--localization edge collapses every monomial.
   Therefore any Frobenius-faithful branch must retain exponent data in a
   separate object and prove its comparison independently. At each fixed
   semilocal stage, the faithful Weyl-multiplier representation of C16 supplies
   such a branch. Prove its compatibility with sheaf restrictions and its
   extension to the compactified coefficient diagram.
2. **Coefficient transport.** Construct an archimedean derived extension
   \(\mathscr A_{\mathrm{ar}}\) of \(\mathscr A_{\mathrm{src}}\), with local
   boundary equal to the Gamma term. Then construct
   \[
     \mathscr B
     =
     R\widetilde\Theta_\ast L\pi^\ast\mathscr A_{\mathrm{ar}}
   \]
   on \(\widetilde{\operatorname{Pic}}\).
3. **Relative object.** Let
   \(\widetilde X_\eta\simeq C_{\mathbb Q}\) be full generic stratum,
   put \(Z_\eta=\widetilde\Theta(\widetilde X_\eta)\), and let
   \(i_\eta:Z_\eta\hookrightarrow\widetilde{\operatorname{Pic}}\). Construct
   \[
     C_{\mathrm{rel}}
     =
     \operatorname{Fib}\!\left(
       R\Gamma(\widetilde{\operatorname{Pic}},\mathscr B)
       \to
       R\Gamma(Z_\eta,Li_\eta^\ast\mathscr B)
     \right).
   \]
   Prove that generic-point subtraction matches the
   \(2h(1)\log\lambda\) counterterm.
4. **Euler-sector comparison.** Construct a cup-compatible equivariant map
   from existing divisor-free prime--Gamma packet cohomology into
   \(H^1(C_{\mathrm{rel}})\).
5. **Source continuation.** Extend its packet/resolvent classes to
   \(\beta_z\) on full continued source domain. Xi zeros may not index a basis,
   quotient, or topology.
6. **Hodge descent.** Embed existing rectangular/Gamma-rank source Hodge core
   cup-isometrically. Prove relative relation subspace is closed and
   \(J_0\)-stable, so \(J_0\) descends to antiunitary \(J^2=-1\) and
   \(\operatorname{tr}(x\smile Jx)\) is faithful.
7. **Faithful globalization.** Prove source-open restriction maps are
   unnormalized, isometric, and injective on every negative-detecting
   direction. Measured convergence is insufficient.
8. **Exact comparison.** Prove, without divisor-side positivity,
   \[
     \left\|
       a\beta_z+b\beta_w
     \right\|^2
     =
     \operatorname{Re}\mathcal E(z,w;a,b)
   \]
   on the full continued two-pole domain.
9. **RH extraction.** Apply the existing unconditional Lean theorem
   `riemannHypothesis_iff_ccmContinuedTwoPoleSourcePassivity`.
10. **Formalization.** Only after Steps 1--8 have a dependency-closed paper
   proof, formalize exact definitions and implications in Lean, then run
   direct leaf checks and one final module audit.

Hostile acceptance tests are mandatory. Construction must reject shifted-Xi
completions, Helson prime-phase twists, indefinite functional-equation
pairings, density-normalized traces, escaping negative strata, and
divisor-defined Hilbert spaces before inspecting their zeros.

## 19. Honest completion status

`[FORMALIZED]` Field-one doctrine atlas is complete at stated method-neutral
interface.

`[LEAN-PROVED]` Ordinary integral scalar extension of a spherical monoid stalk
cannot equal arithmetic localization. A canonical augmentation--localization
comparison exists, but formally identifies every monomial; this closes one
RP0 subroute and records its exact positive survivor.

`[PAPER-PROVED]` At every fixed semilocal stage containing \(p\), spherical
exponents act faithfully by unitary additive-character multipliers, preserving
\(p\)-perfection and scaling covariance. Abstract, archimedean, generic
finite-place, and the canonical normalized all-depth conductor-\(\mathbb
Z_p\) character at every prime are Lean-proved. Canonical restricted
finite-adele character assembly, local constancy, nontriviality, and the
finite-adele Weyl composition law are also Lean-proved. Diagonal-product
compatibility is Lean-proved on every fixed-prime lattice
\(\mathbb Z[1/p]\), which is the exponent group required by each perfection
stage, and a formal primary-decomposition theorem upgrades it to every
rational denominator. Algebraic real--finite tensor assembly, a canonical
nonzero integral finite Bruhat vector, contraction to the archimedean factor,
finite-character primitivity, and faithfulness of the full semilocal action
are Lean-proved. The finite-adele multiplier is Lean-proved unitary on Haar
\(L^2\), with exact compatibility on embedded Bruhat tests, and the full
real--finite product phase is Lean-proved unitary on product-Haar \(L^2\).
The algebraic Schwartz--Bruhat tensor now maps canonically into that product
\(L^2\); the map is injective and exactly intertwines both Weyl actions.
Its pulled-back pre-Hilbert completion is Lean-proved canonically isometric
to the closed algebraic image, and the Weyl action extends unitarily with
exact ambient intertwining. Equality of that closed image with all product
\(L^2\), comparison with any independently defined factorwise completed
Hilbert tensor product, and sheaf compatibility remain open.

`[LEAN-PROVED]` Multiple exact implications and equivalences from faithful
positivity/Hodge naturality to RH are present in repository.

`[OPEN CORE]` No audited source construction currently proves either global
continued two-pole passivity or a positive flow-natural arithmetic Hodge
operator. Therefore RH has not been proved by this route. Claiming completion
now would rename RH-equivalent positivity as an axiom.

Goal closes only when one lane constructs its missing global object without
Xi-divisor input, proves faithful positivity and exact comparison on paper,
formalizes those proofs unconditionally, and invokes an existing RH consumer.

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
- Alain Connes and Caterina Consani,
  [*On the Jacobian of \(\overline{\operatorname{Spec}\mathbb Z}\)*](https://arxiv.org/abs/2602.15941).
- Alain Connes and Caterina Consani,
  [*On the Absolute Geometry of \(\operatorname{Spec}\mathbb Z\)*](https://arxiv.org/abs/2606.06604).
- Alain Connes and Caterina Consani,
  [*Weil positivity and Trace formula, the archimedean place*](https://arxiv.org/abs/2006.13771).
- Igor V. Nikolaev,
  [*Geometry of \(\mathbf F_1\) and Cuntz--Krieger algebras*](https://arxiv.org/abs/2606.22010).
- Luqiao Xu,
  [*Localization and Affine Schemes over F₁*](https://arxiv.org/abs/2607.04843).
