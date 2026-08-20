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


## Card 1 — the multiplicative transfer

`LogDerivRelationSubgroup` builds the bridge from the additive classification (owned) to `G_m`:
`logDerivHom` is the logarithmic derivative as a group homomorphism `F^x -> (F, +)`, and
`logDerivRelationSubgroup c = comap logDerivHom (jetRelationAddSubgroup c)` identifies the
multiplicative relation subgroups as preimages of the additive ones.

What remains on the multiplicative side is the converse: that every proper differential algebraic
subgroup of `G_m` is of this form.  That needs the image of a differential algebraic group under a
differential-algebraic homomorphism to be differential algebraic, i.e. elimination in `DCF_0` -- the
same model-theoretic input the tensor-square `sigma`-simplicity step needs.  Those two, plus the
`GL_2` case, are now the whole gap between the corpus and Dreyfus's normal form.


## Card 1 — plan correction

The item "sigma-simplicity of the tensor square" recorded earlier was wrong: `R ⊗_K R` is not
sigma-simple (it is `R ⊗_C C[G]`, whose sigma-ideals are the ideals of `C[G]`).  What the Galois
correspondence needs is the *ideal correspondence*, and `SigmaIdealConstantCoefficients` shows it is
pure algebra: for a family of constants linearly independent over a sigma-simple base, every
sigma-ideal element has an associate with constant coefficients.  No model theory is involved.

Revised remaining list for card 1:

1. The passage from the ideal correspondence to `C`-points of the Galois group — the
   Nullstellensatz over an algebraically closed constant field.
2. The converse on the multiplicative side (every proper differential algebraic subgroup of `G_m`
   is a `logDeriv` relation subgroup) — needs elimination in `DCF_0`.
3. The `GL_2` case of Cassidy's classification.
4. Dreyfus's normal form and its analytic realization (periodic meromorphic constants).


## Card 1 — item (1) closed

`NullstellensatzPoint` supplies the weak Nullstellensatz and its matrix form, so the passage from
the ideal correspondence to `C`-points of the Galois group is no longer missing.  Remaining:

2. the converse on the multiplicative side (every proper differential algebraic subgroup of `G_m`
   is a `logDeriv` relation subgroup) — elimination in `DCF_0`;
3. the `GL_2` case of Cassidy's classification;
4. Dreyfus's normal form and its analytic realization (periodic meromorphic constants).


## Card 1 — assembled state and the next construction

`SigmaConstantsDisjointness` shows linear disjointness of the constants follows from
`sigma`-simplicity, so all ingredients of the torsor module isomorphism `R ⊗_K R ≅ R ⊗_C E` are now
present:

* `exists_tensor_comparison_matrix` — `Z` exists, invertible, with constant entries;
* `adjoin_tensor_comparison_eq_top` — `Z`'s entries and `1/det Z` generate `R ⊗_K R` over `R ⊗ 1`;
* `basisIndependentOver_of_constants` — a `C`-basis of the constants stays `R`-independent;
* `exists_constant_coeff_mem_sigmaIdeal` — the `sigma`-ideal correspondence;
* `exists_matrix_point_of_finiteType` — the Galois group has `C`-points.

**Next construction**: assemble these into the module isomorphism `R ⊗_K R ≅ R ⊗_C E` (spanning plus
independence gives an `R`-basis of constants), then specialise at a `C`-point to obtain the
`K`-algebra map `R ⊗_K R → R` whose right component is a difference automorphism of `R`.  That is
`R^G = K`, the Galois correspondence.

A cross-module audit imported all twenty-five new modules together and re-elaborated every capstone;
no conflicts.

For item (4), `LinearOdeBohrSpectrum.bohrSpectrum_finite_of_linearOde` is the corpus entry point:
an almost-periodic solution of a nontrivial constant-coefficient linear ODE has finite Bohr
spectrum, which is the exponential-polynomial shape Dreyfus's normal form asserts.


## Card 1 — the specialisation bridge

`DifferenceSpecialization` supplies the bridge from a point of the Galois group to an element of it:
`rightComponent` of a specialisation `R ⊗_K R → R` fixing the left copy is a `K`-algebra
endomorphism, commutes with `σ` when the specialisation does, and sends `Y` to `Y · ψ(Z)` with
`ψ(Z)` invertible.

So the only structural item left in the Galois correspondence is the module decomposition
`R ⊗_K R ≅ R ⊗_C E` — spanning (`adjoin_tensor_comparison_eq_top`) plus independence
(`basisIndependentOver_of_constants`) give a `C`-basis of constants that is an `R`-basis of the
tensor square; the specialisation is then base change along a `C`-point
(`exists_algHom_of_finiteType_of_isAlgClosed`).  That construction, and then items (2), (3), (4),
are what remain.


## Card 1 — the torsor decomposition is built

`TorsorDecomposition` closes the structural item: `R ⊗_C E ≅ A` from generation plus independence,
with the injectivity coming from a general lemma (a linear map sending a basis to an independent
family is injective).  Both hypotheses are supplied for the Picard–Vessiot tensor square by
`adjoin_tensor_comparison_eq_top` and `basisIndependentOver_of_constants`.

The Galois correspondence is now an assembly step: decompose, take a `C`-point
(`exists_algHom_of_finiteType_of_isAlgClosed`), base change to a specialisation, and read off the
automorphism with `DifferenceSpecialization`.  Then items (2) `G_m` converse, (3) `GL_2`, and
(4) Dreyfus's normal form remain.


## Card 1 — the Galois-correspondence chain is complete as general lemmas

`TorsorPointSpecialization` supplies `specializationOfPoint`, the base change of a `C`-point along
the torsor decomposition, with its two computation rules (identity on the base, evaluation on the
constants).  The full chain now exists as general lemmas:

    exists_tensor_comparison_matrix  →  Z constant, invertible
    adjoin_tensor_comparison_eq_top  →  generation
    basisIndependentOver_of_constants →  independence
    tensorDecompositionEquiv          →  R ⊗_K R ≅ R ⊗_C E
    exists_algHom_of_finiteType_of_isAlgClosed → a C-point of E
    specializationOfPoint             →  R ⊗_K R → R, identity on the left copy
    rightComponent(_commutes, _fundamental) → the difference automorphism

What remains for the correspondence is instantiation bookkeeping at the concrete Picard–Vessiot
data, then items (2) `G_m` converse, (3) `GL_2`, (4) Dreyfus's normal form.


## Card 1 — points separate

`PointsSeparate` adds `eq_zero_of_forall_algHom_eq_zero`: on a reduced finite-type algebra over an
algebraically closed field, an element killed by every point is zero (Nullstellensatz + Jacobson).

The route to `R^G = K` is therefore complete as general lemmas, with one remaining input:
reducedness of the constants algebra `E` — in characteristic zero this is Cartier's theorem for the
Galois group scheme, and it is the next thing to build or to carry as a named classical input.

Then items (2) `G_m` converse, (3) `GL_2`, (4) Dreyfus's normal form remain.


## Card 1 — separation with module coefficients

`PointsSeparateModule` upgrades separation from `E` to `M ⊗_C E` by a finite-dimensional duality
argument, which is what the Galois correspondence actually needs.  The separation half of
`R^G = K` is therefore complete as general lemmas.

Still carried: reducedness of the constants algebra `E` (Cartier in characteristic zero).  Then
items (2) `G_m` converse, (3) `GL_2`, (4) Dreyfus's normal form.


## Card 1 — parameterized quotients

`ParameterizedPicardVessiotQuotient` gives `exists_sigmaDeltaSimple_quotient`: every proper doubly
stable ideal lies in a maximal one whose quotient carries both operators, is doubly simple, and has
commuting descended operators.  That is the parameterized analogue of the difference PV quotient.

Next on that side: the `σ`-`δ` coordinate ring of a fundamental matrix (mirror of
`DifferenceCoordinateRing`, with the jet variables carrying the derived action `σ(δ^k X) =
δ^k((A X))`).  Then the parameterized Galois group, Cassidy's `GL_2` case, and Dreyfus's normal form.


## Card 1 — parameterized PV existence

`ParameterizedPicardVessiotExistence` gives the σδ analogue of the abstract PV existence theorem:
a nontrivial σδ-ring with an invertible fundamental matrix has a doubly simple quotient keeping that
matrix, with commuting descended operators.

The parameterized ring-theoretic layer is now: σδ-ideals and their maximal ones, the descended
derivation, doubly simple quotients, existence with a fundamental matrix, and the fact that the
Galois matrix has entries in a differential field of constants.

Remaining: the concrete σδ-coordinate ring (so the abstract existence applies to a given system);
reducedness of the constants algebra (Cartier); the `G_m` converse; the `GL_2` case; Dreyfus's
normal form.


## Card 1 — the σδ-coordinate ring

Corpus finding: `GaloisForLFunctions.DifferentialPolynomialOver` already builds the differential
polynomial ring over a *differential* coefficient field with its total derivation
(`differentialPolynomialOverDerivation`).  Only the difference operator was missing.

`SigmaJetCoordinateRing` adds it: `sigmaJetCoordHom σ A` with `σ (δ^k X_ij) = δ^k ((A X)_ij)`, and
`sigmaJetCoordHom_commutes` proving it commutes with the derivation — a generator check plus one
induction, no Leibniz combinatorics, because the definition is the forced one.

Remaining on that side: invertibility of the action (the `DifferenceCoordinateRing.sigmaCoordEquiv`
computation transported through the jets), then localization at the determinant and the
parameterized Galois group.  Plus reducedness (Cartier), the `G_m` converse, `GL_2`, and Dreyfus's
normal form.


## Card 1 — the σδ-coordinate ring is invertible

`SigmaJetCoordinateEquiv` proves `sigmaJetCoordHom_comp_eq_id`: the difference action on the
differential coordinate ring is invertible, the inverse being the same construction for `σ⁻¹` and
the entrywise `σ⁻¹`-image of `A⁻¹`.  On jet variables the check reduces to the zeroth jet because
both actions commute with the derivation.

Remaining on the parameterized side: localization at the determinant (mirror of
`DifferenceAwayLocalization`), then the parameterized Galois group.  Plus reducedness (Cartier),
the `G_m` converse, `GL_2`, and Dreyfus's normal form.


## Card 1 — derivations on localizations

`LocalizationDerivation` fills a mathlib gap: a derivation extends to *any* localization, by the
dual-numbers graph argument.  The corpus already had the fraction-field case, but the parameterized
coordinate ring is localized at the determinant only — localizing to a field would make the ring
simple and destroy the PV ideal.

With `DifferenceAwayLocalization` both operators now live on the localized differential coordinate
ring.  Remaining: assembling those into the concrete parameterized PV ring, the parameterized Galois
group, reducedness (Cartier), the `G_m` converse, `GL_2`, and Dreyfus's normal form.


## Card 1 — the σδ-coordinate ring is a σδ-ring

`SigmaJetCoordinateAutomorphism` packages the difference action as a ring automorphism commuting
with the total derivation.  The inverse composition follows from the same theorem applied to the
inverse system.

Chain on the parameterized side now: differential polynomial ring over a differential base
(corpus) → difference action (`SigmaJetCoordinateRing`) → invertibility (`SigmaJetCoordinateEquiv`)
→ automorphism (`SigmaJetCoordinateAutomorphism`) → both operators on the localization at the
determinant (`LocalizationDerivation`, `DifferenceAwayLocalization`) →
`exists_parameterizedPicardVessiot_of_fundamentalMatrix`.

Remaining: the transport bookkeeping to the localization, the parameterized Galois group,
reducedness (Cartier), the `G_m` converse, `GL_2`, Dreyfus's normal form.


## Card 1 — commutation transports to the localization

`LocalizationDerivationExt` gives two mathlib gaps: derivations of a localization are determined by
their values on the base, and commutation of a difference operator with a derivation transports from
the base to the localization (conjugate the derivation by the automorphism and apply uniqueness).

The σδ structure therefore transports to the localization at the determinant.  Remaining: the
parameterized Galois group, reducedness (Cartier), the `G_m` converse, `GL_2`, Dreyfus's normal form.

Naming note: `conjDerivation` is already used in four corpus files (inside sub-namespaces); the new
declaration is `automorphismConjDerivation` to keep the umbrella clean.


## Card 1 — the parameterized Galois representation

`ParameterizedGaloisRepresentation` gives the faithful representation of the parameterized Galois
group in invertible matrices over the *differential* field of constants, by restricting the
difference representation along `parameterizedAut_le_differenceAut` and reading the target off
`galoisMatrix_deriv_mem_sigmaConstants`.

That is the last structural piece before the classification itself.  Remaining: reducedness of the
constants algebra (Cartier), the `G_m` converse, the `GL_2` case of Cassidy, and Dreyfus's normal
form with its analytic realization.


## Card 1 — the derivation on the tensor square

`TensorSquareDerivation` puts the derivation on `R ⊗_K R` (same semilinear descent as the difference
operator) and proves the two commute there.  That is the parameterized analogue of
`DifferenceTensorTorsor`, so the parameterized torsor argument now has its setting.

Remaining: reducedness (Cartier), the `G_m` converse, `GL_2`, Dreyfus's normal form.


## Card 1 — parameterized side complete up to the classification

`ParameterizedTensorTorsor` gives the parameterized comparison matrix: entries fixed by the
difference operator on the tensor square, and their derivatives too.  So the Galois group's
coordinates are differential coordinates — the object Cassidy's classification is about.

The parameterized side now runs end to end: σδ-coordinate ring and its automorphism → localization
carrying both operators → parameterized PV quotient → parameterized Galois representation over a
differential field of constants → derivation on the tensor square → parameterized comparison matrix.

Remaining, all classification/analysis rather than structure: reducedness (Cartier), the `G_m`
converse, the `GL_2` case of Cassidy, Dreyfus's normal form and its analytic realization.


## Card 1 — parameterized specialisation

`ParameterizedSpecialization` closes the parameterized bridge: a specialisation of the tensor square
commuting with both operators has a right component commuting with both, hence lies in
`parameterizedAut`.  The derivation half is one line (`δ 1 = 0`).

Remaining, all classification/analysis: reducedness (Cartier), the `G_m` converse, the `GL_2` case of
Cassidy, Dreyfus's normal form and its analytic realization.


## Card 1 — Cassidy additive, evaluated

`CassidyAdditiveEvaluated` evaluates the corpus's coordinate-ideal Cassidy theorem at a point: a
nonzero additive differential Hopf ideal vanishing on a family forces a nonzero finite
constant-coefficient linear relation among its jets.  That is the form a hypertranscendence argument
consumes, and it matches `jetOperator`.

Classification side now: additive case owned and evaluated; multiplicative relation subgroups
identified as preimages under `logDeriv`.  Missing: the multiplicative converse and `GL_2`.
Plus reducedness (Cartier) and Dreyfus's normal form with its analytic realization.


## Card 1 — reducedness closed without Cartier

The route through Cartier's theorem is abandoned; it is not needed.  What the Galois correspondence
wants is `IsReduced` for a subalgebra of `R ⊗_K R`, and that follows from a general theorem now
proved in the tree:

* `TensorProductAlgClosedReduced` — over an algebraically closed field, reduced ⊗ reduced is
  reduced (points separate, after expanding against a basis of the second factor);
* `TensorProductCharZeroReduced` — `isReduced_tensorProduct_of_charZero`: in characteristic zero,
  reduced ⊗ reduced is reduced.  Route: finitely generated subalgebras of the algebraic closure are
  finite separable field extensions; finite separable extensions keep a reduced base reduced via
  `Algebra.FormallyUnramified.isReduced_of_field` at each prime; then descend.
  No transcendence basis and no separably-generated theory is needed — that plan was longer than
  necessary.
* `SigmaConstantsReduced` — the application: `R ⊗_K R` reduced for `σ`-simple `R`, hence every
  subalgebra reduced, hence points of the Galois coordinate algebra separate.

Also landed: `PrimitiveNilpotentCharZero` (a nilpotent primitive element of a characteristic-zero
algebra vanishes) — the Cartier-style obstruction, kept because it is the natural statement about
primitives and is reusable.

Remaining on card 1: the `G_m` converse, the `GL_2` case of Cassidy, Dreyfus's normal form and its
analytic realization.


## Card 1 — the isomonodromy obstruction is closed

The classification consumes two obstructions for the rank-two order module: irreducibility (no
rational Riccati solution — already in the tree) and non-isomonodromy (no rational compatible
derivation).  The second is now proved:

* `RatFuncShiftDegree` — the finite difference of a polynomial has degree `deg p - 1` with leading
  coefficient `deg p · lead p`; hence the unit shift difference of a rational function drops the
  degree at infinity by **exactly** one when the degree is nonzero, and by at least two when the
  degree is zero and the function is nonconstant.
* `RatFuncShiftDegreeCalculus` — the "zero or bounded" degree calculus (`intDegree 0 = 0` is larger
  than a negative degree, so plain `≤ max` lemmas are unusable).
* `BesselOrderIsomonodromyObstruction` — `besselOrder_no_rational_delta_structure`.

Mechanism: the first compatibility identity forces the trace `P + σP + b σQ` to be shift invariant,
hence constant; that bounds `deg (b σQ)`.  The combination `σ²Q - Q + b (P - σP) = c` then has one
summand of exactly degree `deg P` and the other of degree at most `max 0 (deg P) - 2`, so it can
never be a nonzero constant.

Remaining on card 1: Cassidy for `SL₂` (Zariski-dense proper differential algebraic subgroups are
conjugate to the constant points), the parameterized Galois correspondence step "solution
differentially algebraic ⟹ parameterized group proper", and the analytic realization.


## Card 1 — the analytic isomonodromy theorem

`DeltaStructureCompatibility` (abstract) plus `BesselOrderMeromorphicIsomonodromy` (analytic)
transport the rational obstruction to the genuine meromorphic carrier:

**for `s > 0` there are no rational `P, Q` with `∂K_ν(s)/∂ν = P K_ν(s) + Q K_{ν+1}(s)`.**

Ingredients: the corpus's meromorphic translation/derivation compatibility for `ℂ(ν)`, the corpus's
meromorphic order recurrence, the new linear independence of `K_ν(s)` and `K_{ν+1}(s)` over `ℂ(ν)`
(from the rational Riccati obstruction), and the new degree-at-infinity obstruction.

`DeltaStructureLinearOde` gives the converse: a rational compatible derivation would force a linear
differential equation of order two, so the criterion is exactly right.

Remaining on card 1: the parameterized classification itself — Cassidy for `SL₂`, the parameterized
Galois correspondence, and the identification of the difference Galois group of the order module.


## Card 1 — differential algebra foundations started

The remaining chain (Cassidy for `SL₂`, the parameterized Galois correspondence) rests on
Kolchin's differential algebraic geometry.  The corpus already owns the Kolchin topology
(`DifferentialKolchinClosure`) and Ritt rank (`DifferentialPolynomialRank`).  Three new modules
start the ideal theory, which mathlib does not have at all:

* `RadicalDifferentialIdeal` — Ritt's lemma (`mul_deriv_mem_of_mul_mem`: in a radical differential
  ideal, `a b ∈ I` forces `a δb ∈ I`) and the characteristic-zero Keigher property
  (`deriv_mem_radical`: over a `ℚ`-algebra the radical of a differential ideal is differential,
  by a descent trading one power of `x` for two powers of `δx`).
* `RadicalDifferentialIdealGeneration` — `radicalDifferentialIdeal S`, the smallest radical
  differential ideal containing `S`, with its radicality, differentiality and minimality, and the
  product law via the colon ideal.
* `RadicalDifferentialIdealPrime` — `mul_mem_of_forall_mul_mem` (the product law for sets) and
  `mem_or_mem_of_maximal_not_radDiffFG`: **a maximal non-finitely-generated radical differential
  ideal is prime**, the Zorn step of Ritt's basis theorem.

Next in this layer: the Zorn existence step (a chain of radical differential ideals has a radical
differential union, still not finitely generated), then the characteristic-set argument that a
prime radical differential ideal in a differential polynomial ring is finitely generated.


## Card 1 — Ritt's basis theorem reduced to the prime case

`RadicalDifferentialIdealZorn` supplies the Zorn half (`exists_maximal_not_radDiffFG`: a chain of
radical differential ideals has a radical differential supremum which is still not finitely
generated, because a finite generating set already lies in one member), and
`RittBasisPrimeReduction` combines it with the primality step:

```text
radDiffFG_of_prime_radDiffFG
    if every prime radical differential ideal is finitely generated as a radical differential
    ideal, so is every radical differential ideal
```

What remains of Ritt--Raudenbush is exactly the prime case: a prime radical differential ideal of a
differential polynomial ring is finitely generated.  That is the characteristic-set / Ritt-reduction
argument; the corpus already owns the ranking layer (`DifferentialPolynomialRank`).


## Card 1 — the shift span

`BesselOrderShiftSpan` upgrades the analytic isomonodromy theorem: every integer shift
`K_{ν+n}(s)` lies in the `ℂ(ν)`-span of `K_ν(s)` and `K_{ν+1}(s)` (two-directional recurrence,
`Int.induction_on` on the pair), hence

**`∂K_ν(s)/∂ν` is not a rational combination of any finite family of integer shifts.**


## Card 1 — the separant

`DifferentialSeparant.exists_separant_decomposition`: for a scalar differential polynomial `A` of
order `n`, `δA = S_A · y_{n+1} + B` with `ord B ≤ n`, where `S_A = ∂A/∂y_n`.

Proof device worth reusing: to induct over a differential polynomial of bounded order, present it as
`rename Subtype.val A'` for `A' : MvPolynomial {p // p.2 ≤ n} K` via
`MvPolynomial.supported_eq_range_rename`; then `MvPolynomial.induction_on`'s `mul_X` case only ever
meets variables of order at most `n`, which is exactly the bookkeeping the direct induction fails to
maintain.

Next: the initial (leading coefficient in the leader), pseudo-division by `A` and by `δ^k A`, the
Ritt reduction algorithm, and hence the prime case of Ritt's basis theorem.


## Card 1 — Ritt order reduction complete

`DifferentialSeparantIterate` → `DifferentialPseudoDivision` → `RittOrderReduction`:

* every proper derivative `δ^{k+1} A` is `S_A · y_{n+k+1} + (order ≤ n+k)`;
* pseudo-division against a polynomial linear in the top jet costs only powers of `S_A` and leaves a
  remainder of strictly lower order (induction over the jets of order ≤ m, so the only variable to
  eliminate is `y_m` itself);
* iterating gives `S_A^e · F ≡ R  (mod derivIdeal A)` with `ord R ≤ ord A`.

Remaining in this layer: the degree-lowering step — pseudo-division by `A` itself in the leader,
costing powers of the initial.  That needs the univariate view of a differential polynomial in its
leader (`MvPolynomial.optionEquivLeft` plus `Equiv.optionSubtypeNe`, or a direct induction on the
leader degree).  With it, the prime case of Ritt's basis theorem closes.


## Card 1 — Ritt's basis theorem proved; a duplication corrected

**Correction.**  Four modules written earlier this session (`DifferentialSeparant`,
`DifferentialSeparantIterate`, `DifferentialPseudoDivision`, `RittOrderReduction`) duplicated
machinery the tree already owned in more general form — `PseudoDivisionCommRing` has
`exists_pseudoDivision`, `iterate_eq_separant_mul_add`, `exists_higherJet_reduction_step`,
`diffPolyIterateIdeal`, `exists_phaseOne_reduction`, `exists_ritt_reduction` and
`exists_initial_separant_powers_mem_diffPolyIterateIdeal`, and `DifferentialKernelCharacteristic`
has the initial, the separant, and `initial_not_mem` / `separant_not_mem` for a rank-minimal element.
The four modules were deleted and unwired.  **Search the corpus before building a sub-layer, not
just before opening a card.**

What was genuinely missing was the *ideal theory*, and it is now complete:
`radDiffFG_differentialPolynomial` — every radical differential ideal of `K{y}` is the radical
differential ideal of a finite set.

Assembly: Zorn gives a maximal non-finitely-generated radical differential ideal `M`; the product law
makes it prime; `Ideal.exists_minimal_scalarDifferentialPolynomialRank_ne_zero` gives a rank-minimal
`A ∈ M`; `initial_not_mem` and `separant_not_mem` put `h = I_A · S_A` outside `M`; the corpus's
reduction gives `h^j Q ∈ {A}` for every `Q ∈ M` (with `hreduced` supplied by rank minimality); and
`isRadDiffFG_of_saturation` collapses `M` onto a finite set.


## Card 1 — the Kolchin topology is Noetherian

`RadicalDifferentialIdealACC.acc_radicalDifferentialIdeal` (ACC on radical differential ideals, from
Ritt's basis theorem) and `KolchinNoetherian.dcc_isKolchinClosedOver` (DCC on Kolchin closed sets of
one differential coordinate, by the vanishing-ideal/zero-locus Galois connection the tree already
owned).

This is the last piece of general differential-algebraic-geometry infrastructure that is cheap.  The
remaining chain for card 1 is genuinely the classification: differential algebraic subgroups of
`SL₂` (Cassidy) and the parameterized Galois correspondence.


## Card 1 — the obstruction in matrix form

`BesselOrderJetModule` states the isomonodromy obstruction the way the literature does: the first
jet system `[[A, δA],[0,A]]` splits under a block-unipotent gauge iff `σ(B)A - AB = -δA` is solvable,
and for the Bessel companion `A = [[0,1],[1,c(ν+1)]]` it is not.  The four entrywise identities
reduce to the two scalar ones already refuted.

Next on the critical path (all searched, none present in the tree): the parameterized Galois
correspondence linking non-splitting of the jet tower to growth of the differential transcendence
degree, and Cassidy's classification for `SL₂`.


## Card 1 — the obstruction is intrinsic

`MatrixLogarithmicDerivative` (Kolchin's `ℓδ` with the crossed-homomorphism law),
`IsomonodromyGaugeInvariance` (a gauge carries a connection to a connection — proved with `T`
cleared, so the identity needs no invertibility), and `BesselOrderIntrinsicObstruction`
(`ratShift_deriv`: the unit shift commutes with the rational derivation, transported through the
meromorphic embedding; hence `besselOrder_no_gauge_delta_structure`).

Result: **no system gauge equivalent to the Bessel order companion over `ℂ(ν)` admits a
connection** — the obstruction is a property of the difference module.

Searched before building each of these; `ratShiftEquivBy` exists as a ring automorphism but carries
no derivation-commutation lemma, and the tree had no gauge invariance for difference modules.


## Card 1 — the constant-Galois direction

`ConstantGaloisConnection.exists_base_logDerivMatrix_of_galois_constant`: if every Galois matrix
`Y⁻¹ φ(Y)` is `δ`-constant and the invariants of the Galois action are the base, then `ℓδ Y` has
entries in the base — the system is isomonodromic.

Mechanism: the crossed-homomorphism law for `ℓδ` makes the contribution of a constant Galois matrix
vanish, so `ℓδ Y` is Galois invariant.

This closes the *translation* half of the endgame.  What remains: Cassidy's classification (which
produces the conjugating element making the Galois matrices constant) and the parameterized Galois
correspondence (which supplies `R^G = K`).  Searched before building; neither the naturality of `ℓδ`
nor this statement existed in the tree.


## Card 1 — the Galois correspondence was already in the tree

Searching before building paid off twice more.  A draft of "points of the torsor separate ⟹
invariants are the base" was **discarded unbuilt**: the tree already has
`PositiveDimensionalInvariantGeneration.AffineTorsorCoaction.coinvariant_eq_range` (faithfully-flat
descent), `PointSeparatingTorsorAction.fixedByPoints_eq_range`, and
`AffineRationalPointSeparation` (Nullstellensatz points).

The one genuine gap was that those are stated for a torsor over a **field**, and a Picard--Vessiot
ring is not one.  `RingTorsorCoinvariance.coinvariant_eq_range_of_canonical` supplies the
coefficient-ring form; mathlib's descent equalizer already covers commutative rings, and faithful
flatness over a field is automatic.

Next step for item (ii): instantiate it — build the canonical torsor map for the PV ring from
`tensorDecompositionEquiv` (`R ⊗_C E ≅ R ⊗_K R`) together with
`Algebra.TensorProduct.cancelBaseChange` (`R ⊗_K (K ⊗_C E) ≅ R ⊗_C E`), and check the two embedding
conditions.  Item (i), Cassidy for `SL₂`, remains untouched.


## Card 1 — correction, and joint injectivity over a ring

**Correction to the previous entry.**  The module discarded last turn was *not* a duplicate.  The
corpus's `fixedByPoints_eq_range` **assumes** joint injectivity of the point evaluations;
`AffineRationalPointSeparation` proves that injectivity only for field coefficients.  Since a
Picard--Vessiot ring is not a field, the injectivity with ring coefficients was genuinely missing.
It is now `TorsorPointSeparation.eq_zero_of_forall_torsorPointHom_eq_zero` /
`eq_of_forall_torsorPointHom_eq`.

Lean note: the concrete `A = R ⊗_K R` form of the statement fails to elaborate when
`Algebra C (R ⊗_K R)` is taken as a free instance — the synthesized `IsScalarTower` then refers to a
different algebra structure.  The abstract-`A` form avoids this; the concrete instantiation should be
done where the Picard--Vessiot objects are concrete, not with free instance variables.


## Card 1 — Cassidy for `sl₂`, graded case proved

`CassidySl2Graded`:

* `eq_span_singleton_of_mul_mem_range` — two nonzero `k`-subspaces of a field whose product lands in
  `k` are `k`-lines.  This is the computational heart: bracket closure `[v e, w f] = (v w) h` forces
  `V·W ⊆ k`, and then dividing by a common element of `W` puts ratios in `k`.
* `graded_cassidy_sl2` — a graded `k`-Lie subalgebra of `sl₂(U)` with both root spaces nonzero is
  conjugated to `sl₂(k)` by `diag(1, v₀)`.

Worth remembering: the normalisation needs **no square root**.  The textbook conjugator
`diag(λ, λ⁻¹)` requires `λ² = v₀⁻¹`; `diag(1, v₀)` does the same job over any field.

Remaining for Cassidy: reduce the general case to the graded one — produce a torus, i.e. conjugate a
Zariski-dense differential algebraic subalgebra so that it is graded by the diagonal.


## Card 1 — Cassidy's reduction, step one

`Sl2RegularElement.exists_det_ne_zero_of_mem_span`: a `k`-subspace whose `U`-span contains a matrix
of nonzero determinant contains one itself.  The determinant is a quadratic form; vanishing on a
subspace forces its polarisation to vanish there (closure under addition), and both then vanish on
the whole span by induction.

So the Zariski-dense subalgebra contains a regular semisimple element.  Step two of the reduction:
conjugate that element to the diagonal — over an algebraically closed `U` this is diagonalisation of
a `2 × 2` traceless matrix with nonzero determinant, giving `diag(μ, -μ)`.  Step three is the delicate
one: the subalgebra is only a `k`-subspace, so `ad(X)`-stability does **not** by itself split it into
root spaces (the eigenvalues `±2μ` need not lie in `k`).  That is where Cassidy's argument constructs
the field of multipliers `k' = {c ∈ U : c L ⊆ L}` first.


## Card 1 — Cassidy for `sl₂` is proved

`Sl2DiagonaliseRegular.exists_conj_toral_of_det_ne_zero` (step two),
`Sl2ToralClassification.cassidy_sl2_of_toral` (the toral case) and
`CassidySl2Classification.cassidy_sl2` (the general case).  All axiom-clean.

The reduction that made it work: **the line-stabiliser hypothesis**, `c A ∈ L` with `0 ≠ A ∈ L`
forces `c ∈ C`, replaces the multiplier field.  With it, three brackets suffice — the naive
"multiplier field" route is circular, because showing `mult(L) ⊆ C` implies the grading needs the
grading first.  The line-stabiliser form is what differential algebraicity actually delivers, since
`{c : c A ∈ L}` is a solution set of a linear differential system.

Also recorded: over an algebraically closed `C` the conjugator `diag(1, v₀)` needs no square root,
and the whole argument needs `C` algebraically closed exactly once — to pass from `μ² ∈ C` to
`μ ∈ C`.  Without it the theorem is false (`su(2) ⊂ sl₂(ℂ)` over `ℝ` is not conjugate to `sl₂(ℝ)`).

Next: the transfer lemma — a nonzero linear differential system has a solution space of finite
dimension over the constants — which is what supplies the line-stabiliser hypothesis in the
application.


## Card 1 — Cassidy in usable form, and the differential transfer

`CassidyMatrixAlgebra` (associative and group versions), `DifferentialSolutionSpace` (minimal
support for `v′ = A v`, the companion reduction, the power-family relation) and
`DifferentialConstantsCollapse` (a ring of solutions is constant).

The important structural finding: **the classification only needs the line stabiliser of elements
with nonzero determinant**, and for an associative algebra that follows from the stabiliser of `1`
alone, via `Z² = -det(Z)·1` for traceless `Z`.  So the group form of the theorem has one hypothesis:
the scalars `c` with `c · 1` in the `C`-span of the group are constants.  That is a *ring*, which is
what makes the differential transfer work — finite dimensionality over the constants alone is not
enough to force an element into `C`, but finite dimensionality of a *ring* is.

Next: the Lie-level bridge.  When `L` is cut out by linear differential equations, each stabiliser
`{c : c Y ∈ L}` is a solution set, hence bounded over the constants; the iterated bracket identity
`ad(Z)³ = 4δ ad(Z)` then puts a whole power family `c (4δ c²)^k` inside one stabiliser, so `4δ c²`
and `4δ` are algebraic over `C`, and `c ∈ C`.  That converts the boundedness the differential
structure gives into the line-stabiliser hypothesis the classification takes.


## Card 1 — the classification is complete in differential form

`BaseFieldCollapse`, `Sl2LineStabiliserBridge`, `DifferentialCassidyClassification`.

End product: `constant_conjugate_of_differentialSolution` — a multiplicative set of `2 × 2`
matrices containing `1`, spanning `M₂(U)` over `U`, whose scalar stabiliser `{c : c·1 ∈ span_C G}`
solves one monic linear differential equation, is conjugated by a single matrix into `M₂` over the
constants.

Remaining chain for the card, in order:

1. the Galois group of the Bessel system spans `M₂` over `U` — this is Burnside from the
   irreducibility the corpus already proves (`DifferenceOperatorFactorization`);
2. the scalar stabiliser solves a linear differential equation — this is what differential
   algebraicity of `K_ν(s)` gives, through the parameterized Galois representation;
3. constant Galois matrices ⟹ isomonodromy (`ConstantGaloisConnection`, owned);
4. isomonodromy is impossible (`BesselOrderIntrinsicObstruction`, owned).


## Card 1 — Burnside lands, classification now takes irreducibility

`BurnsideTwoByTwo.mem_of_irreducibleAction` and
`DifferentialCassidyClassification.constant_conjugate_of_irreducible`.

The remaining Galois-side obligation is now exactly one arrow: **no first-order factorization ⟹ the
Galois action on the solution space has no invariant line**.  Everything after it is proved.


## Card 1 — the irreducibility arrow, in two halves

`DifferenceSemiInvariantSolution` closes the second half: tensor identity ⟹ base Riccati solution.

The first half is a separation statement to build next:

```text
eq_zero_of_forall_specialization_eq_zero :
  if every K-algebra map R ⊗_K R → R that is the identity on the left copy kills w, then w = 0
```

Route (all inputs owned): the torsor decomposition `R ⊗_K R ≅ R ⊗_k E` writes `w = Σ r_j ⊗ b_j` in
a `k`-basis of `E`; each `k`-point `χ` of `E` gives such a specialisation, and its value on `w` is
`Σ χ(b_j) r_j`; `PointsSeparateModule.eq_zero_of_forall_point_smul_eq_zero` then forces every
`r_j = 0`.

Applied to `w = v₁ ⊗ v₂ - v₂ ⊗ v₁` for a solution vector `v = (y, σ y)`, this converts
"every Galois element scales `v`" into `y ⊗ σ y = σ y ⊗ y`, and the Riccati contradiction closes
irreducibility — the last hypothesis the classification needs.


## Card 1 — irreducibility arrow closed

`TorsorSpecializationSeparation` (separation of specialisations) and
`DifferenceIrreducibilityCriterion` (no Riccati ⟹ no semi-invariant solution).

Every general theorem the endgame needs is now proved.  What remains is instantiation:

1. build the concrete Picard--Vessiot data for the Bessel recurrence — the constants subalgebra `E`
   of the tensor square with its basis, the generation and independence hypotheses;
2. identify the Galois matrices with the specialisations, so "no semi-invariant solution" becomes
   the irreducibility hypothesis of `constant_conjugate_of_irreducible`;
3. derive the scalar-stabiliser differential equation from differential algebraicity of `K_ν(s)`;
4. feed the constant Galois matrices into `ConstantGaloisConnection` and contradict
   `BesselOrderIntrinsicObstruction`.


## Card 1 — abstract endgame closed

`isomonodromy_of_no_riccati_of_differentialSolution` is the capstone: for a second-order difference
equation over a base field, with

* no Riccati solution over the base,
* a separating set of Galois points,
* a scalar stabiliser of the Galois monoid solving one monic linear differential equation,

the system carries a connection over the base — the exact statement the Bessel intrinsic obstruction
refutes.

Remaining: (i) the scalar-stabiliser differential equation from differential algebraicity
(Cassidy additive, owned in evaluated form as
`exists_nonzero_jet_linear_relation_of_additiveHopfIdeal`); (ii) the concrete Bessel
Picard--Vessiot data.


## Card 1 — the base field has to be enlarged, and the obstruction now travels

An architectural finding that determines the rest of the card.

The parameterised theory is **vacuous over `ℂ(ν)`**: the `σ`-constants of the base are `ℂ`, the
parameter derivation kills them, and a differential algebraic subgroup over a derivation-trivial
field is just an algebraic subgroup.  Concretely, the fundamental theorem of parameterised
Picard--Vessiot theory fails there — for `σ y = x y` the automorphism `ψ ↦ ψ + a` fixes nothing new
yet `ψ = δy/y` is not rational.  So the base must be `C(ν)` with `C` a differentially closed field
containing `ℂ`: then `K^σ = C` carries a nontrivial derivation and the theory is meaningful.  The
statement proved is then non-differential-algebraicity over `C(ν)`, which is *stronger* than over
`ℂ(ν)`, so nothing is lost.

That forces the obstruction to hold over the larger base, and it now does:

`GaloisForLFunctions.HTGeometry.RatFuncFieldShift` — the unit shift `X ↦ X+1` and its whole degree
calculus over an arbitrary field of characteristic zero (37 declarations: the finite difference of a
polynomial, the exact degree drop of the shift difference, shift-invariance implies constancy).

`GaloisForLFunctions.HTGeometry.BesselOrderFieldObstruction` — the scalar and matrix forms of
"the Bessel order recurrence carries no rational connection", over any such field.

Remaining for the card:

1. a `Differential` structure on `C(ν)` extending a given derivation on `C` with `δν = 1`, and its
   commutation with the shift;
2. the concrete Picard--Vessiot data over `C(ν)`;
3. the scalar-stabiliser differential equation from differential algebraicity (Cassidy additive);
4. a separating set of differential points — the Kolchin Nullstellensatz over a differentially
   closed `C`, for which the corpus already owns Ritt--Raudenbush and Kolchin Noetherianity.


## Card 1 — the differential structure on the enlarged base

`RatFuncTotalDerivation`: `D(f) = coeffDeriv f + (d/dX) f` on `K[X]`, extended across the fraction
field, giving `Differential (RatFunc K)` in which `K` keeps its own derivation and the coordinate has
derivative one — with `coordinateTotalDerivation_base` and `coordinateTotalDerivation_X` as the two
computational facts.

Reuse note: the coefficientwise derivation already existed (`PolynomialTotalDerivative.coeffDeriv`,
`TwoCylinderDifferential.coeffDeriv_mul`, `coeffDerivHom`) — the search index did not surface it for
the query "derivation on polynomial ring extending base derivation", so a duplicate was built and
then discarded.  When looking for a construction, grep the corpus for the *operation name* as well.

Lean note: `Derivation ℤ (RatFunc K) (RatFunc K)` has an instance diamond — `Algebra ℤ (RatFunc K)`
resolves to `RatFunc.instAlgebraOfPolynomial` rather than `Ring.toIntAlgebra`.  Building the
derivation over `ℚ` and closing with
`letI : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _; Derivation.restrictScalars ℤ` is what elaborates.

Next: the shift as a ring equivalence over a general field, and the commutation `σ ∘ δ = δ ∘ σ`
(two derivations agreeing on `K[X]` agree on `K(X)`, by `derivation_ext_of_fractionRing`).


## Card 1 — the base field is complete, and the route to the last hypothesis

`RatFuncFieldShiftEquiv` (the shift as a ring automorphism, via translations composing additively)
and `RatFuncShiftDerivationCommute` (`σ ∘ δ = δ ∘ σ` on `K(X)`, by conjugating the derivation and
comparing on `K[X]`) finish the difference-differential base field over an arbitrary differential
coefficient field.  The conjugation reuses `SemilinearFractionField.conjDerivation` rather than
rebuilding it.

What the endgame still needs is `hsep`: a separating set of *differential* points of the Galois
coordinate ring.  That is Kolchin's Nullstellensatz, and it needs the constants `C` to be
differentially closed — which is exactly why the base had to be enlarged.  The route is:

1. a proper radical differential ideal has a zero in a differential field extension (Ritt's prime
   decomposition, which the corpus owns as `RadicalDifferentialIdealPrime` and `RittBasisTheorem`);
2. iterate to a differentially closed extension, as one builds an algebraic closure;
3. Kolchin's Nullstellensatz: over such a field the differential points of a finitely generated
   differentially reduced algebra separate.

The alternative route — the prolongation tower with only the classical Galois correspondence —
needs the Picard--Vessiot dimension theorem (`trdeg = dim G`) instead, and the tower analysis that
shows the transcendence degree keeps growing when the isomonodromy class is nonzero.  Route 1 is
the one the endgame is already built for.


## Card 1 — the weak differential Nullstellensatz

`RadicalDifferentialIdealMaximal` (a maximal proper radical differential ideal is prime, so every
proper one lies in a prime differential ideal) and `DifferentialFieldSolution`
(`exists_differentialField_hom_of_ne_top`: a proper radical differential ideal of a differential
`ℚ`-algebra is killed by a differential ring map to a differential field).

That is step 1 of the differential closure.  Step 2 is the iteration: for a differential field `F`,
adjoin solutions of *all* consistent systems over `F` at once — the differential polynomial ring in
the union of the variable sets modulo the sum of the ideals, which stays proper because the
quotients are nonzero algebras over a field in disjoint variables — and take the union of the chain.
Step 3 is Kolchin's Nullstellensatz over the resulting field, which is what supplies `hsep`.


## Card 1 — the differential closure, step by step

`DifferentialSystemSolution.exists_point_of_ne_top` is the engine: a proper radical differential
ideal in the differential polynomial ring over a differential field has a solution point in a
differential field extension.

The closure is then built as mathlib builds an algebraic closure:

1. **Joint consistency.**  For systems in disjoint variables the quotient of the sum ideal is the
   tensor product of the quotients over the base field, hence nonzero; so the sum of proper
   differential ideals in disjoint variables is proper, and its radical is a proper radical
   differential ideal (Ritt's lemma keeps it differential).
2. **One step.**  Take the differential polynomial ring in the variables of *all* consistent systems
   over `F`, with the radical differential ideal generated by all of them; any element of it
   involves finitely many systems, so step 1 makes it proper.  A maximal proper radical differential
   ideal above it is prime, and the fraction field of the quotient solves every system over `F`.
3. **Iterate.**  Repeat `ω` times and take the direct limit; every system over the limit has its
   coefficients in some stage, hence a solution one stage later.  The limit is differentially closed.
4. **Kolchin.**  Over a differentially closed field the differential points of a finitely generated
   differentially reduced algebra separate — which is `hsep`.


## Card 1 — the differential closure is built

The four steps of the closure plan are Lean-complete.

`DifferentialPolynomialRename` (renaming differential variables commutes with the total derivation;
the kernel of a differential map to a field is a radical differential ideal) and
`DifferentialPolynomialBaseChange` (extending the coefficients commutes with the total derivation;
the three evaluation identities: renamed, coefficient-extended, and transported along a differential
map of the target).

`DifferentialFieldExtension` bundles a differential field extension — field, derivation, structure
map, and the statement that the structure map is differential — so an extension is a value that can
be returned, composed and iterated.  `DifferentialJointSolvability` proves that a system consistent
over the base stays solvable over any extension (the coefficient extension of a differential ideal
is differential, and stays proper over a field, so its radical is a proper radical differential
ideal), and that finitely many consistent systems are jointly solvable in one extension.

`DifferentialClosureStep`: the differential polynomial ring on the variables of *all* consistent
systems over `F` at once carries the radical differential ideal generated by all of them, and it is
proper — membership is witnessed by finitely many generators, hence finitely many systems, which are
jointly solvable, and evaluation at a joint solution is a differential map to a field killing those
generators.  A point of it solves every consistent system over `F` in a single extension.

`DifferentialClosureTower`: the tower of iterated one-step extensions, and its union.  The field
structure is the directed union of fields; the derivation comes from the universal property applied
to the **dual numbers** of the union — the maps `x ↦ (x, x′)` are compatible along the tower, so
they lift to a ring map whose first component is the identity and whose second component is a
derivation extending every stage.  (That trick is what avoids having to define a non-ring-hom map on
a colimit.)

`DifferentialClosureClosed`: the union is differentially closed — a finite system there has finitely
many coefficients, hence descends to a stage; consistency descends because a relation would push
forward; and the next stage solves it.

`RadicalDifferentialIdealAvoiding`: for a radical ideal, missing an element is missing all its
powers, so Zorn and Ritt's product law give a *prime* differential ideal avoiding a prescribed
element, hence the weak differential Nullstellensatz in the form separation needs — a differential
map to a differential field killing the ideal but not the element.

Lean note: `Ring.DirectLimit` carries its own `CommRing`, and `Field.DirectLimit.field` is a
reducible non-instance built on it.  Declaring both a `CommRing` and an unrelated `Field` instance
on the union makes instance search fail on `DualNumber` (two incompatible `Semiring` paths).  The
fix is to declare the field as `{ theCommRingInstance, Field.DirectLimit.field … with }`, so that
the ring structure of the field literally is the one instance search finds.

Remaining for the card: Kolchin's Nullstellensatz (differential points of a finitely generated
differentially reduced algebra separate, over a differentially closed field), then the concrete
Bessel Picard--Vessiot data and the scalar-stabiliser differential equation.


## Card 1 — Kolchin, the differential Galois points, and the constants field

`KolchinNullstellensatz`: over a differentially closed field, a nonzero element of a finitely
generated differentially reduced algebra survives some differential point.  The proof presents the
algebra by generators and relations and turns a differential map into a *finite* differential system
over the base — the defining relations, the first-order equations for the derivatives of the
generators, and the Rabinowitsch equation — which differential closedness then solves inside the
field.  Hence the differential points separate.

`DifferentialGaloisPoint`: the specialisation of the torsor at a differential point commutes with
the derivation.  The elements of the tensor square where the two agree form a subalgebra containing
the image of the ring and the constants subalgebra, so generation forces the identity everywhere; at
`1 ⊗ x` that is exactly the statement that the Galois automorphism is differential.  (The derivation
on the tensor square was already owned: `TensorSquareDerivation`.)

`DifferentialGaloisSeparation`: both hypotheses of the isomonodromy endgame — the separating set and
the differentiality of its Galois automorphisms — are now discharged, leaving
`isomonodromy_of_no_riccati_of_differentiallyClosed`, whose only inputs are the difference equation,
the absence of a base Riccati solution, and the differential constraint on the scalar stabiliser.

`DifferentiallyClosedAlgClosed`: a differentially closed field is algebraically closed (the
algebraic closure is separable in characteristic zero, so the derivation extends to it, and a root
there is a solution of an order-zero differential system), and its constants are algebraically
closed (differentiating the defining relation of a root of a polynomial with constant coefficients
gives the separant times the derivative of the root).

So `diffClosure ℚ` — or the differential closure of any characteristic-zero differential field —
supplies every hypothesis the endgame makes on the field of constants: `IsAlgClosed`, `CharZero`,
`IsAlgClosed (differentialConstants ·)`, and `IsDifferentiallyClosed`.

What remains for the card is the concrete instantiation: the Picard--Vessiot ring of the Bessel
order recurrence over `C(ν)` (the corpus owns `exists_picardVessiot_system`,
`exists_parameterizedPicardVessiot_of_fundamentalMatrix`, `exists_picardVessiot_no_new_constants`,
the torsor generation and the comparison matrix), and the bridge from differential algebraicity of
`K_ν(s)` to the differential constraint on the scalar stabiliser (Cassidy additive, owned in
evaluated form).


## Card 1 — what the endgame's scalar hypothesis really needs (route analysis)

The endgame hypothesis `hsol` — the scalars `x` with `x • 1` in the `C^δ`-span of the Galois monoid
solve one monic linear differential equation — is **not** a consequence of differential algebraicity
alone.  Counterexample shape: a group `SL₂(C^δ) · Z` with `Z` the scalars whose logarithmic
derivative solves a linear equation.  Every solution of the associated system is differentially
algebraic (its logarithmic derivative is), yet the `C^δ`-span of `Z` is not the solution set of any
single linear equation, and indeed the system is only isomonodromic *after a scalar twist*.  So the
endgame is inapplicable to a system whose Galois group has a nontrivial differential scalar part.

For the Bessel order recurrence that part is absent, and for a structural reason worth recording:
the companion matrix `!![0,1;1,b]` has determinant `-1`, so `σ(det Y) = -det Y`, hence `(det Y)²` is
`σ`-invariant and lies in the constants; every Galois matrix therefore has determinant `±1` and
every *scalar* Galois matrix `x·1` has `x² = ±1`.  The scalar part of the Galois group is contained
in the fourth roots of unity — in particular it is differentially constant, and no scalar twist is
available.

That leaves the genuine remaining content, which is Cassidy's classification in its
differential-algebraic form rather than in the corpus's "bounded" form:

* **From differential algebraicity to a nonzero differential ideal.**  If a solution is
  differentially algebraic over `K`, so is the whole Picard--Vessiot ring (the Galois translates of
  a solution span the solution space by irreducibility, and the differentially algebraic elements
  form a differential field).  For a `σ`-invariant element the relation ideal over `K` is a
  `σ`-ideal, so the minimal-support engine
  (`SigmaIdealConstantCoefficients.exists_nonzero_constant_coeff_mem_sigmaIdeal`) descends a nonzero
  relation to the constants `C`.  Every entry of the comparison matrix therefore satisfies a nonzero
  differential polynomial over `C`, and since the differential points are `C`-algebra maps commuting
  with the derivation, *every Galois matrix entry lies in a fixed proper differential algebraic
  subset of `C`*.
* **From the ideal to boundedness.**  The multiplier field of the differential Lie algebra is an
  additive differential subgroup; the group's nonzero differential ideal restricts to a nonzero
  differential Hopf ideal on it (the Hopf property of a vanishing ideal of a subgroup is the
  differential Nullstellensatz for a product, now available through Kolchin), and Cassidy's additive
  classification — owned as
  `CassidyAdditiveEvaluated.exists_nonzero_jet_linear_relation_of_additiveHopfIdeal` — turns that
  into the linear differential equation the corpus's `BoundedOverBase` wants.

So the remaining chain is: (P1) `σ`-descent of differential relations; (P2) differential
algebraicity of the whole ring from one solution; (P3) the differential algebraic group layer —
vanishing ideal, Hopf property, and the reduction of the multiplier field to an additive subgroup.


## Card 1 — the descent of relations to the constants

`DifferentialRelationSigmaDescent`, `DifferentialRelationConstants`

```text
differentialPolynomialSigma                the coefficientwise shift of differential polynomials
differentialPolynomialEvalOver_sigma       evaluation intertwines it with a shift fixing the point
exists_sigmaFixed_relation                 a relation satisfied by a `σ`-invariant point can be
                                           taken with `σ`-invariant coefficients
exists_preimage_of_coeffs                  a polynomial with coefficients in a subring descends
exists_nonzero_constants_relation          **hence a relation over the constants**
eval_relation_of_differentialHom           and a relation over the constants travels along any
                                           differential map of algebras over them
```

So for a `σ`-invariant element of the tensor square which is differentially algebraic over the base,
there is one nonzero differential polynomial over `C` that every differential point sends its value
into the zero set of.  That is step (P1) of the remaining chain; what is left is (P2) differential
algebraicity of the whole ring from one solution, and (P3) the differential algebraic group layer
turning the resulting proper differential algebraic set into the boundedness Cassidy's
classification consumes.
