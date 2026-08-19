# Stage-3 formalization programme for three `2-fully-proven/other` cards

- **ID:** `three-other-cards-stage3-formalization-programme`
- **Stage:** 1-in-progress (ledger; not a research card)
- **Type:** FORMALIZATION LEDGER
- **Targets:**
  1. `bessel-order-intensity-hypertranscendence`
  2. `jet-horizon-translation-gauge-classification`
  3. `embedded-manin-horizon-isogeny-reconstruction`

Each of the three is blocked on a *foundational* layer, not an assembly step.  This file records
the exact blocked statement, the chosen route, and the layer order, so the work survives
compaction.

## Card 2 — jet-horizon translation-gauge classification

**Blocked on (card's own boundary):** DCF_0 model theory — differential genericity, dtrdeg
invariance, quantifier elimination giving the fixed-field identity `(12)`, and the Picard--Vessiot
identification of the torsor layers `(7)`.

**Route found (2026-08-19): the model theory is avoidable.**  The whole theorem is purely
differential-algebraic once the *Taylor arc* is used instead of the DCF embedding groupoid.

Let `(F, δ)` be a differential field, `ℚ ⊆ F`, constants `C`.  The Taylor morphism

```text
τ : F → F⟦T⟧,   τ(a) = Σ_n (δ^n a / n!) T^n
```

is an injective ring homomorphism with `d/dT ∘ τ = τ ∘ δ`.  For `z ∈ F^m` and `P ∈ C[X]`,
`τ(P(z)) = P(τ z)`, so the jet sequence of `z` *is* a formal arc on the locus `Y` of `z`.

Then:

* `h ∈ ker δ^n`  ⟺  `τ(h)` is a polynomial of degree `< n` in `T`.
* If `σ` is a differential `C`-embedding fixing `δ^n z`, then `h = σ z − z ∈ ker δ^n`, and
  `P(τ z + τ h) = 0` for every `P ∈ I(Y)`.
* If `τ z` is a *generic point of `Y`* over the coefficient field `Ω ⊇ C⟨h⟩` — i.e.
  `ker(Ω[X] → Ω⟦T⟧, X ↦ τ z) = I(Y)·Ω[X]` — then `P(X + τh) ∈ I(Y)·Ω[X]`, i.e.
  `Y + τh = Y`, hence every coefficient of `τ h` lies in `A = Stab_trans(Y)`.  This is `(3)`.
* `A = 0` therefore forces `σ z = z`, hence `σ = id`, hence `H_n(Y) = F`: this is `(4)`, with no
  quantifier elimination.  The infinitesimal form (derivations commuting with `δ` instead of
  embeddings) gives the same conclusion and identifies `Der^δ_{H_n}(F) ≅ A ∩ ker δ^n`.
* The quantitative form is `trdeg(C⟨z⟩ / C⟨δ^n z⟩) = n · dim A`, which with the already-formalized
  cylinder splitting `(5)` reduces to the `A = 0` base case plus the free-jet count for the
  additive factor — that is the torsor tower `(7)`, `(8)`.

**Lean layer order.**

1. `DifferentialTaylorMorphism` — τ as a ring hom, injectivity, `τ ∘ δ = d/dT ∘ τ`,
   `τ (aeval z P) = aeval (τ ∘ z) P`, `ker δ^n` ⟺ polynomial of degree `< n`.  [layer 1]
2. `DifferentialLocusTranslation` — the locus ideal of a point, translation stabilizer of an
   ideal, and: a translation carrying the locus into itself is an equality (Noetherian surjective
   endomorphism).  [layer 2]
3. `DifferentialGenericPoint` — the genericity predicate `ker(Ω[X] → …) = I·Ω[X]`, and its
   consequences.  [layer 3]
4. `JetHorizonEmbeddingRigidity` — `(3)`.  [layer 4]
5. `JetHorizonReconstruction` — `(4)`, both directions.  [layer 5]
6. `JetHorizonTorsorTower` — `(6)`, `(7)`, `(8)` and the trdeg formula.  [layer 6]

Already in the tree: `JetHorizonTranslationGauge` (cylinder splitting `(5)`, gauge `(3)`/`(9)`
kernel half), `DerivationIterateLeibniz`, `DifferentialTranscendenceDegree`,
`AffineZariskiClosureOver`, `DifferentialKolchinClosure`.

## Card 3 — embedded Manin horizon

**Theorem A** (`Stab_A(T_A) = A^♯`) is short once the Manin map is available as a group
homomorphism with kernel `A^♯` and the tail is `K⟨μ_A(a)⟩`.

**Theorem B** imports Manin-kernel rigidity (Casale--Freitag--Nagloo Fact 5.6, ultimately
Hrushovski's dichotomy).  Unconditional Lean requires that rigidity itself.  Layer order to be
fixed after card 2; the tree already owns `MultiplicationTailFixedField`,
`ManinKernelKolchinClosure`, `AbelianManinHorizonTheorem`, `DifferentialKolchinClosure`.

## Card 1 — Bessel order/intensity hypertranscendence

**Blocked on:** Dreyfus's classification (parameterized Picard--Vessiot for difference
equations).  Everything else in the card is already unconditional in the tree, and
`BesselOrderDreyfusNormalForm` states the reduction machine-checked.

Rank-two reformulation that the Lean layer must reach: with `u(ν) = K_ν(s)`, `v(ν) = K_{ν−1}(s)`,
`a = 2ν/s`, the shift acts `σu = a u + v`, `σv = u`; a second solution is `w_ν = e^{iπν} I_ν(s)`
with Casoratian `−e^{iπν}/s`.  Differential algebraicity of `u` makes `N = ℂ(ν)⟨u,v⟩` a `σδ`-field
of finite transcendence degree over `ℂ(ν)`; the classification is what converts that into the
growth normal form.  No elementary substitute has been found: Hölder's method needs the shift to
act by a *rational multiple*, which fails at rank two.

## Card 2 — what is now Lean-proved, and the exact remaining pieces

Seven new modules, all axiom-clean (`[propext, Classical.choice, Quot.sound]`):

| Module | Content |
|---|---|
| `DifferentialTaylorMorphism` | `τ a = Σ (δ^n a / n!) T^n` as an injective ring hom `R → R⟦T⟧` with `d/dT ∘ τ = τ ∘ δ`; arcs of polynomial expressions; `ker δ^n` = low-degree arcs |
| `AffineTranslationStabilizerRigidity` | surjective endomorphism of a Noetherian ring is injective; a translation carrying a locus into itself carries it onto itself |
| `AffineConstantVectorFieldTranslation` | translation is the exponential of `D_h = Σ h i ∂/∂X i`; an ideal stable under `D_h` is stable under translation by `h` |
| `JetHorizonFirstDepthRigidity` | chain rule `D(P(z)) = (D_h P)(z)`; a constant derivation direction is a translation symmetry; depth-one gauge |
| `JetHorizonAllDepthGauge` | no primitive of one ⟹ `ker δ^n` = constants ⟹ depth-independent rigidity, derivation and endomorphism forms |
| `JetFieldNoPrimitiveOfOne` | the free differential rational field has no primitive of one; both rigidity statements on `JetField C ι` |
| `JetHorizonCylinderGauge` | the translation automorphism of a free generator fixes every positive jet and moves the generator, so `C⟨δ^n y⟩ ⊊ C⟨y⟩` for a pure additive cylinder |
| `DifferentialGenericPointHorizon` | prolonged ideals, jet translation, differential genericity, and: for a differentially generic point a coordinate lying in `C⟨δ^{n+1} z⟩` forces the corresponding component of every translation symmetry to vanish — hence `H_n ⊊ F` whenever the stabilizer is nontrivial, for arbitrary `Y` |
| `DifferentialPrimitiveDescent` | an element algebraic over a differential subfield whose derivative lies in that subfield lies in it, when there are no new constants (minimal-polynomial second-coefficient argument); both the abstract-base and the intermediate-field forms |
| `DifferentialTranscendenceCrux` | if a differential field is generated over a derivation-closed intermediate field by elements whose derivatives lie in it, and is not algebraic over it, it carries a nonzero derivation over the constants killing that field and commuting with the derivation |
| `JetHorizonReconstruction` | depth-one reconstruction: a translation-rigid locus is recovered from its first derivatives |

**Lean engineering note.**  Do *not* introduce `Differential ↥K` for an `IntermediateField` via
`derivationClosedDifferential` inside these proofs: the resulting instance stack makes `rfl`-level
defeq checks blow past a million heartbeats.  State the intermediate-field lemmas without any
differential structure on the subfield (see `mem_of_isAlgebraic_of_deriv_mem`).

**Remaining for card 2.**

1. **Done** (existence half, general `Y`): `DifferentialGenericPointHorizon`.
2. *Field equality `H_n = F` when `A = 0`.*  The route is now fixed and needs no genericity:

   * **Crux.**  If `K ⊆ F` are differential fields, `F = K(y)` with `δ y_i ∈ K` for every `i`, and
     some `y_i` is transcendental over `K`, then there is a nonzero `K`-derivation of `F`
     *commuting with `δ`*.  Construction: take a transcendence basis of `F/K` inside the family
     `y` (`exists_isTranscendenceBasis_subset`), prescribe constant values on it
     (`DerivationPrescription.exists_derivation_prescribed`), and observe that `⁅δ, D⁆` kills `K`
     and the basis, hence kills the whole field because `F` is algebraic over `K(basis)`
     (`JetLevelAlgebraicallyClosed.derivation_eq_zero_of_isAlgebraic`).
   * **Depth one.**  With `K = H_1 = C⟨δ z⟩` the hypothesis `δ z_i ∈ K` holds for every `i`.  So
     `A = 0` (which kills every `δ`-commuting derivation, `JetHorizonFirstDepthRigidity`) forces
     `F` algebraic over `H_1`, and then `DifferentialPrimitiveDescent` forces `F = H_1`.
   * **Induction.**  Once `F = H_j`, the pair `(H_{j+1}, F)` is again a depth-one situation for the
     point `δ^j z`, and the collapse `ker δ^n = C` of `JetHorizonAllDepthGauge` shows any
     `δ`-commuting derivation killing `δ^{j+1} z` also kills `δ^j z`, contradicting the crux.
     Hence `F = H_{j+1}`, and `F = H_n` for every `n`.
3. **Done** (cylinder bookkeeping `(6)`): `JetHorizonCylinderDecomposition`.
4. **Done** (upper half of the torsor law `(7)`): `JetHorizonAdditiveLayer` — a layer automorphism
   moves the forgotten jet by a *constant*, displacements add under composition, and an
   automorphism is determined by its displacement.  So the layer gauge group embeds in `G_a` over
   the constants.
5. *Remaining.*  The surjectivity half of `(7)`: every constant really is realized by a layer
   automorphism.  Over a **constant** base this is already in the tree —
   `ScalarAdditiveDifferentialTorsor.scalarAdditiveDifferentialGaloisGroupEquiv` gives the full
   additive differential Galois group of `F⟨q⟩ / F⟨q′⟩` — but its `hconst : ∀ c : F, c′ = 0`
   restricts the base to constants, whereas the card's layers sit over the non-constant base
   `C⟨z⟩`.  The construction that generalizes is transport along `T ≅ RatFunc L` for `q`
   transcendental over `L` with `L(q) = T`, composed with
   `RatFuncTranslationFixedField.ratFuncTranslationEquiv`; nothing in that argument uses
   constancy of the base.

   **Attempted and abandoned route, with the reason.**  Building the translation as
   `(hq.aevalEquivField.trans coord).symm.trans (shifted coordinate)` does not survive kernel
   checking: `AlgebraicIndependent.aevalEquivField` is built from `AlgEquiv.ofInjectiveField`, so
   its `.symm` goes through `Function.surjInv`, i.e. `Classical.choice`, and every lemma
   application that mentions that inverse — even `AlgEquiv.symm_apply_apply` — makes the kernel
   time out deterministically.  The route that avoids this is to construct the translation with an
   *explicit* two-sided inverse: transport `RatFuncTranslationFixedField.ratFuncTranslationEquiv`
   (whose inverse is the opposite translation, given definitionally) along an
   `IsFractionRing`-based identification of `L(q)` with `RatFunc L`, so that no `surjInv` ever
   appears in the term.

## Card 3 — Lean work started

`GaloisForLFunctions.HTGeometry.DGroupHorizonStabilizer` proves Theorem A inside the corpus's
`DGroupPresentation` framework: the stabilizer of the differential field generated by the
logarithmic coordinates of a point is exactly `dGroupSharp P = {g | ell g = 0}`.  The additivity of
the displacement is no longer hypothesized — it is `DGroupPresentation.ell_mul`.

Remaining for card 3: realize the Manin homomorphism of an abelian variety over a differential
field as a `DGroupPresentation` (then `dGroupSharp` is the Manin kernel), and Manin-kernel rigidity
for Theorem B.

## Card 3 — status after audit

`DifferentialHorizonInterface.differentialTranslationStabilizer_differentialAdjoin_eq_kernel`
already *is* Theorem A in abstract form: if translation moves the quotient coordinates by the
Manin coordinates of the translating point, the stabilizer of the generated differential field is
exactly the common kernel.  What is missing is not that deduction but the identification of that
kernel with `A^♯`, i.e. Manin-kernel theory for abelian varieties over a differential field, and —
for Theorem B — Manin-kernel rigidity (Casale--Freitag--Nagloo Fact 5.6, resting on Hrushovski's
dichotomy).  That is the largest of the three foundations.

## Card 1 — Lean work started

`GaloisForLFunctions.HTGeometry.DifferenceSolutionSpace` is the first layer of the difference
Picard--Vessiot chain, unconditional and axiom-clean:

```text
differenceConstants σ                     the fixed subfield of a difference field
IsDifferenceSystemSolution σ A v          σ v = A v
exists_differenceConstants_relation       a nontrivial K-relation among solutions of an
                                          invertible system can be replaced by a nontrivial
                                          relation with shift-invariant coefficients
exists_differenceConstants_relation_of_ne_zero   the same with possibly vanishing coefficients
card_le_of_no_differenceConstants_relation       solutions with no nontrivial constant relation
                                          number at most the rank
```

The proof is the classical minimal-support argument: normalize a coefficient to one, apply the
automorphism, use invertibility of the system matrix to see the shifted coefficients again solve,
and subtract — the difference has strictly smaller support, so minimality forces every coefficient
to be a constant.  A corpus search (`Picard-Vessiot ring extension difference equation Galois`,
`difference module shift operator rational function field solution space`,
`linear difference equation fundamental matrix Casoratian`) found nothing of this kind already
present; `DifferenceDifferential.CommutingDifferenceDifferentialField` is the σδ-field structure to
build on for the parameterized theory.

**Next layers.**  Companion-matrix reduction of a scalar order-`n` equation to a system (with the
determinant of the companion matrix, so that invertibility is `a₀ ≠ 0`); difference Picard--Vessiot
rings (σ-simple extensions with a fundamental matrix); the Galois group; then the parameterized
theory with `d/dν` acting, and Cassidy's classification of differential algebraic subgroups of
`GL₂` in the rank-two case the Bessel recurrence produces.

## Card 1 — concrete next steps

The card's only gap is Dreyfus's classification.  Before any Lean work, the corpus search terms to
run are `parameterized Picard-Vessiot`, `difference Galois group`, `Tannakian`, `isomonodromy`;
nothing of the kind is presently in the tree, and mathlib has no Picard--Vessiot theory at all.

The layer order for a from-scratch build is: difference rings and modules over `ℂ(ν)` with the shift;
Picard--Vessiot rings for difference equations (existence and uniqueness over an algebraically
closed field of constants); the difference Galois group as an affine group scheme; then the
*parameterized* version with the derivation `d/dν` acting, whose Galois group is a linear
differential algebraic group; and finally Cassidy's classification of differential algebraic
subgroups of `GL_2` restricted to the rank-two case that the Bessel recurrence produces.  Only the
last step is specific to this card.

## Session audit — 2026-08-19

Fifteen modules added, every one wired into `GaloisForLFunctions.HTGeometry` exactly once, with its
olean built and its capstones `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`):

```text
card 2  DifferentialTaylorMorphism            AffineTranslationStabilizerRigidity
        AffineConstantVectorFieldTranslation  JetHorizonFirstDepthRigidity
        JetHorizonAllDepthGauge               JetFieldNoPrimitiveOfOne
        JetHorizonCylinderGauge               DifferentialGenericPointHorizon
        DifferentialPrimitiveDescent          DifferentialTranscendenceCrux
        JetHorizonReconstruction              JetHorizonCylinderDecomposition
        JetHorizonAdditiveLayer
        JetHorizonTorsorTower
card 1  DifferenceSolutionSpace
card 3  DGroupHorizonStabilizer
```

**A second Lean trap, found the hard way.**  For an *arbitrary* `K : IntermediateField C F`,
deciding `x ∈ (IntermediateField.adjoin ↥K s).restrictScalars C` against `x ∈ adjoin ↥K s` is not
cheap: the `IsScalarTower C ↥K F` path makes `isDefEq` run past two hundred thousand heartbeats,
and `rw [IntermediateField.mem_restrictScalars]` fares no better.  It works when the ambient field
is *definitionally* the restrictScalars (as inside
`JetHorizonReconstruction.derivationClosed_restrictScalars_adjoin`, where `set` keeps the body
visible) and fails when the statement quantifies over the intermediate field.  So the layer
identity `H_j = H_{j+1}(δ^j y)` must be phrased without `restrictScalars` — e.g. as a membership
equivalence proved by `IntermediateField.adjoin_induction` in both directions, never forming the
restricted field.  That reformulation is now carried out: `JetHorizonTorsorTower.mem_differentialAdjoin_iff_mem_adjoin`
and `mem_jetHorizon_iff_mem_adjoin_succ` prove the layer identity as an equivalence of memberships,
by `adjoin_induction` in both directions, and never form the restricted field.  With the horizons
decreasing and each adjoined jet solving `δ X = δ^{j+1} y` in the next horizon, `(7)` now has its
whole structural content: every layer is generated over the next by solutions of that additive
equation, and its gauge group sits inside `G_a` over the constants — exactly `G_a` in the pure
cylinder case.

**Exact remaining work, in the order to attempt it.**

1. *Card 2, `(7)` surjectivity over a non-constant base.*  Everything else on card 2 is proved.
   The pure-cylinder case is already exact (`JetHorizonCylinderGauge`, via the corpus's
   constant-base `translationAutomorphism`); the general case needs the relative construction,
   whose only obstacle is the `surjInv` inside `AlgebraicIndependent.aevalEquivField.symm` (see the
   abandoned route above).
2. *Card 1.*  Companion determinant in general rank, then difference Picard--Vessiot rings, the
   difference Galois group, the parameterized theory, Cassidy's `GL₂` classification.
   `DifferenceSolutionSpace` already supplies the solution-space finiteness and the companion
   reduction, with rank-two invertibility.
3. *Card 3.*  Realize the Manin homomorphism of an abelian variety over a differential field as a
   `DGroupPresentation`; then `DGroupHorizonStabilizer` gives Theorem A with `dGroupSharp` equal to
   the Manin kernel.  Theorem B additionally needs Manin-kernel rigidity.

## Log

- 2026-08-19 — programme opened; model-theory-free Taylor-arc route for card 2 identified.
- 2026-08-19 — card 2: Taylor arc, translation rigidity, constant-vector-field criterion,
  depth-independent gauge rigidity, free-field no-primitive-of-one, and the cylinder gauge all
  Lean-proved; the four remaining pieces listed above.
- 2026-08-19 — card 3: Theorem A's field-theoretic deduction found already present in
  `DifferentialHorizonInterface`; the blocker is Manin-kernel theory, not the deduction.
- 2026-08-19 — card 2: the reconstruction direction of `(4)` is no longer a gap.  The
  transcendence crux (`DifferentialTranscendenceCrux`), the intermediate-field primitive descent
  (`DifferentialPrimitiveDescent.mem_of_isAlgebraic_of_deriv_mem`) and the gauge-trivial
  reconstruction (`JetHorizonReconstruction`) give `H_n = F` for a translation-rigid locus at
  every depth, with no genericity and no model theory; the depth induction uses only the
  `ker δ^n = C` collapse.


## Status 2026-08-19 — two of three cards promoted

**Card 2 `jet-horizon-translation-gauge-classification`: PROMOTED to `3-formalized`.**  The last
missing half was the surjectivity of the layer gauge action `(7)` over a non-constant base.  It is
closed by `GaloisForLFunctions.HTGeometry.JetHorizonAdditiveTorsorLaw`, which also raises the rank
from one to an arbitrary index type, giving the card's `G_a^r` directly:

```text
differentialConstants F                        the constant subfield of a differential field
vectorDerivativeField F q                      F<q'> for a family q
vectorDerivativeField_adjoin_eq_top            T = F<q'>(q) ordinarily
vectorConstTranslationAction_injective/_surjective
vectorAdditiveGaloisGroupEquiv                 Aut_delta(T / F<q'>) = (constants F)^iota
vectorAdditiveGaloisGroupEquivConstantField    = G_a^iota(C)
```

The abandoned `RatFunc` transport route was unnecessary: the corpus already owned
`differentialIndependentTopAlgEquiv`, which builds the translation automorphism directly from
differential independence, for an arbitrary index family, with no `surjInv` anywhere.  The only
real obstruction in `ScalarAdditiveDifferentialTorsor` was the hypothesis `hconst : forall c : F,
c' = 0`, and the observation that removes it is that only constancy of the *translating scalar* is
ever used.

**Card 3 `embedded-manin-horizon-isogeny-reconstruction`: PROMOTED to `3-formalized`.**
`GaloisForLFunctions.HTGeometry.ManinHorizonIsogenyReconstruction` gives the nonorthogonality
relation a concrete definition (an isogeny correspondence: a subgroup of the product projecting onto
both factors with finite kernels), proves it symmetric and reflexive, and proves the elementary half
of Manin-kernel rigidity — a `D`-group homomorphism carries sharp points to sharp points, so an
isogeny of `D`-groups produces a correspondence.  Theorem A holds by the `D`-group structure alone;
Theorem B and the abstract/embedded dichotomy follow.  Hrushovski's dichotomy is carried as the
named hypothesis `hrigidity`, exactly as the parent card
`abelian-multiplication-tail-manin-horizon` carries its seven classical inputs at stage 3.

**Card 1 `bessel-order-intensity-hypertranscendence`: still stage 2.**  Difference Picard--Vessiot
rings now exist in Lean (five modules, all axiom-clean; see the card's own log).  The next layer is
"no new constants" for a base with algebraically closed constants, then the difference Galois group,
then the parameterized theory, then Cassidy's `GL_2` classification.


## Card 1 — the difference Galois foundation, layer by layer

Eleven new modules now exist where mathlib and this repository had no Picard--Vessiot theory at all:

| Module | Content |
|---|---|
| `DifferenceSolutionSpace` | constants of a difference field; solution space of a rank-`n` system has dimension at most `n` over them |
| `DifferenceSigmaSimple` | `sigma`-ideals, maximal ones by Zorn, `sigma`-simplicity, reducedness, **constants of a `sigma`-simple ring form a field** |
| `DifferenceCoordinateRing` | the action `a |-> sigma a`, `X |-> A X` on `K[X_ij]`; an automorphism with explicit two-sided inverse; `det X |-> det A . det X` |
| `DifferenceAwayLocalization` | the action extends to the localization at the determinant |
| `DifferencePicardVessiotQuotient` | a maximal `sigma`-ideal is two-sided stable; the quotient is `sigma`-simple, reduced, with a field of constants |
| `DifferenceSystemPicardVessiot` | **existence of a Picard--Vessiot ring for every invertible linear difference system over every difference field** |
| `DifferenceGaloisMatrix` | linear disjointness of constants; a difference automorphism moves the fundamental matrix by an invertible matrix of constants, multiplicatively |
| `TranscendentalTranslateObstruction` | Chevalley: a transcendental element of a finite-type algebra cannot have all its translates by an infinite set of scalars invertible |
| `DifferenceNoNewConstants` | **no new constants**, algebraic form and algebraically-closed form |
| `DifferenceGaloisRepresentation` | the faithful group homomorphism to `GL_n` over the base |
| `ParameterizedDifferenceGalois` | `sigma`-`delta` ideals, maximal ones, and the fact that the constants form a *differential* field, so the parameterized Galois group is a differential algebraic group |

Every capstone reports `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

**Next, in order.**

1. The torsor property `R ⊗_K R ≅ R ⊗_C C[G]` and the Galois correspondence.
2. Parameterized Picard--Vessiot rings: in a `Q`-algebra, a maximal `sigma`-ideal of a
   `sigma`-`delta` ring is a `delta`-ideal (Hardouin--Singer), so the parameterized ring exists.
3. Cassidy's classification of differential algebraic subgroups of `GL_2`.
4. Dreyfus's growth normal form; the corpus already refutes it for `K_nu(s)` and for the intensity
   in `BesselOrderDreyfusNormalForm`.


## Card 1 — later layers

Four further modules:

| Module | Content |
|---|---|
| `DifferenceCompanionCasoratian` | companion invertibility in every rank (no determinant computation); the Casoratian criterion in both directions |
| `DifferenceOperatorFactorization` | factorization of a second-order difference operator is exactly its Riccati equation; **the Bessel order recurrence is irreducible over `C(nu)`** |
| `DifferencePicardVessiotConstants` | **the Picard--Vessiot ring of an invertible system has exactly the constants of the base** — construction and constants theorem joined |
| `DifferenceFundamentalSolutionSpace` | the solution space is the constant span of the fundamental matrix |

The irreducibility theorem is the first *card-specific* consequence of the new foundation: the
corpus's rational-Riccati obstruction now says that the order recurrence for `K_nu(s)` has no
first-order right factor, so its difference module is irreducible.  That is the hypothesis under
which Cassidy's classification of differential algebraic subgroups of `GL_2` has content.

Remaining, unchanged: the torsor property and Galois correspondence (needs semilinear tensor
products, which mathlib lacks); the parameterized Picard--Vessiot ring; Cassidy's classification;
Dreyfus's normal form.


## Card 1 — the tensor square

`DifferenceTensorTorsor` removes the obstacle recorded above as "needs semilinear tensor products,
which mathlib lacks".  The difference operator on `R ⊗_K R` is built directly with
`TensorProduct.liftAddHom`: the map `x ⊗ y ↦ σx ⊗ σy` is additive in each variable and satisfies
the descent condition `σ(a·x) ⊗ σy = σx ⊗ σ(a·y)` because the twist is by an automorphism of `K`,
so it factors through the tensor product over `K` even though it is not `K`-bilinear.  Ring
multiplicativity follows by double `TensorProduct.induction_on`, and the inverse is the same
construction for `σ⁻¹`.

With that in place, `exists_tensor_comparison_matrix` gives the torsor comparison matrix.  The
remaining half of the torsor property is that `R ⊗_K R` is generated over `R ⊗ 1` by the entries of
`Z` and `1/det Z`, together with `σ`-simplicity of `R ⊗_K R`.

**Umbrella hygiene.**  A full scan of the 161 declarations added for these three cards against every
other `GaloisForLFunctions.HTGeometry` file found two genuine collisions (`tensorShiftHom` in
`CDGATensorShiftHom`, `tensorShiftEquiv` in `CDGARelTensorDescent`); the new declarations were
renamed to `differenceTensorHom` / `differenceTensorEquiv`.  No collisions remain.


## Card 1 — corpus finding that changes the remaining plan

`DifferentialHopfPrimitive.nonzero_additiveHopfIdeal_exists_finite_jet_linear_relation` is already
in the tree: every nonzero additive differential Hopf ideal in characteristic zero contains a
nonzero finite constant-coefficient linear combination of jets.  That is **Cassidy's classification
of differential algebraic subgroups of `G_a`**, in coordinate-ideal form.  `AffineExponentialSubgroups`
owns `additiveRelation_isHopfIdeal` and `torusRelation_isHopfIdeal`; `DGroupBasicInstances` owns
`multiplicativeDGroup`.

So the plan's item "Cassidy's classification" is only partly missing.  What is missing is the
multiplicative transfer (a differential algebraic subgroup of `G_m` is cut out by a linear
differential operator in the logarithmic derivative, by pushing the additive result through
`logDeriv`) and the `GL_2` case.

New modules this round: `TensorSquareEqualizer` (the equalizer of the two embeddings into the tensor
square is the base field; a trivial comparison matrix collapses the Picard--Vessiot ring) and
`QuotientDerivation` (a derivation descends to the quotient by a differential ideal, and the
descended `sigma` and `delta` still commute).
