# Borel's rank theorem, formalized: the programme

- **ID:** `borel-rank-formalization-programme`
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAMME (multi-session)
- **Serves:** `deninger-algebraic-cyclotomic-milnor-amplitude` — its **only** remaining input
- **Supersedes:** the route table of `garland-formalization-programme` (audited unsound 2026-08-18)
- **Created:** 2026-08-18

## Target

For a number field `K`,
\[
 K_2(\mathcal O_K)\otimes\mathbb Q=0,
\]
equivalently the degree-two tame kernel is torsion.  This is Borel's rank computation in the only
form the parent card needs, equivalently Garland's 1971 finiteness theorem.

## Why this is now the *only* target

Two audits fixed the picture:

1. `k2-rank-divisibility-firewall` proves, unconditionally and in Lean, that **no combination of
   finite-coefficient statements can give the rank** — the mod-`m` theory is blind to a uniquely
   divisible summand — and that **finite generation is exactly what restores decidability**
   (`isTorsion_of_fg_of_no_int_quotient`).
2. The card's second alleged blocker, its `(4)`, **does not exist**: the corpus already owns the
   `E_∞` layer in its commutative-differential-graded model (`deninger-character-shape-formality` at
   stage 3, the 79-module CDGA stack, `derivedBaseChange_zigZag`, `freeExteriorCDGAHom`,
   `relTensorCDGA`).  `RHTower.deningerAlgebraicMilnorAmplitude` now states the whole card with the
   tame-kernel statement as its single hypothesis.

So the parent card is exactly one classical theorem from stage 3.

## The route: integral finiteness first, then a mod-`m` bound

```
K₂(𝒪_S) ⊗ ℚ = 0
  ⇐ [F] K₂(𝒪_S) finitely generated        ← the integral input the firewall demands
      ⇐ H₂(SL_n(𝒪_F), ℤ) finitely generated
          ⇐ SL_n(𝒪_F) acts on a contractible complex, cocompactly, with FINITE stabilizers
              ⇐ Ash's well-rounded retract        ← geometry of numbers, NOT analysis
  ⇐ [M] |K₂(𝒪_S)/m| bounded
      ⇐ Merkurjev–Suslin / Tate: K₂(F)/m ≅ H²(F, μ_m^{⊗2})
      ⇐ finiteness of the étale H² with finite coefficients
```

Layer F is the half that is *not* analytic: the well-rounded retract is built from minimal vectors of
lattices, and its cocompactness is Minkowski/Mahler finiteness.  That is the reason this route is
chosen over Borel's own symmetric-space argument, which needs continuous cohomology of Lie groups,
van Est, and Borel–Serre.

## Layer F — progress

### F1. Minimal vectors of a lattice `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/LatticeMinimalVectors.lean` (wired into the `HTGeometry`
umbrella; axiom audit `propext, Classical.choice, Quot.sound`).

```text
discreteSubmodule_isClosed          a discrete ℤ-submodule of a normed space is closed
finite_lattice_inter_of_bounded     ** it meets every bounded set in a finite set **
exists_minimal_norm                 ** a nonzero discrete submodule has a shortest nonzero vector **
```

These are the objects the retract is made of: a lattice is *well-rounded* when its shortest vectors
span, and the well-rounded locus is the complex on which `SL_n(𝒪)` acts with finite stabilizers.
mathlib has `IsZLattice`, `Zspan.setFinite_inter` for the span of a basis, and
`Metric.finite_isBounded_inter_isClosed`; what it does not have is the statement for an arbitrary
discrete submodule, nor the existence of a shortest vector, both of which are proved here.

### F2. Well-roundedness and FINITE STABILIZERS `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/LatticeWellRounded.lean` (wired; axiom audit
`propext, Classical.choice, Quot.sound`).

```text
IsLatticeMinimum, exists_isLatticeMinimum   the length of a shortest nonzero vector, and that it
                                            exists
latticeMinimalVectors                       the shortest vectors
latticeMinimalVectors_finite                ** finite **
latticeMinimalVectors_nonempty              nonempty at the minimum
IsWellRounded                               the shortest vectors span
mapsTo_latticeMinimalVectors                a lattice isometry permutes them
eq_of_eqOn_latticeMinimalVectors            they determine a linear map on a well-rounded lattice
finite_latticeIsometry_of_wellRounded       ** THE ISOMETRY GROUP OF A WELL-ROUNDED LATTICE IS
                                               FINITE **
```

The last is step 4 of the plan and one of the two geometric inputs of the whole layer: it is exactly
why the action on the well-rounded retract has **finite stabilizers**, hence why the equivariant
chain complex is finitely generated over `ℤΓ`, hence why `H_i(Γ, ℤ)` is a finitely generated abelian
group.  The proof is the elementary one — a lattice isometry permutes the finitely many shortest
vectors, and on a well-rounded lattice those span, so the isometry is determined by the permutation,
giving an injection of the isometry group into a finite set of maps.

### Next bricks in Layer F

1. **Mahler/Minkowski compactness**: the set of unimodular lattices with minimum bounded below is
   compact — the *cocompactness* input, the second geometric half.
2. The well-rounded retract itself: the deformation of the space of lattices onto the well-rounded
   locus, and its contractibility.
3. The equivariant cell structure, and the passage `finitely many orbits + finite stabilizers ⟹
   `ℤ` has a resolution by finitely generated `ℤΓ`-modules ⟹ `H_i(Γ, ℤ)` finitely generated`.
4. `H₂(SL_n(𝒪)) → K₂(𝒪)`: Matsumoto, the universal central extension, and homological stability.

## Layer M — not started

Merkurjev–Suslin in weight two, or Tate's class-field-theoretic proof for number fields, followed by
the finiteness of `H²_ét(𝒪_S, ℤ_p(2))`.  By the firewall this layer is *permitted* only in the
presence of Layer F; on its own it can prove nothing about the rank.

## Log

- 2026-08-18 — Programme opened after the `(4)` correction reduced the parent card to a single
  input.  Layer F started: minimal vectors of a lattice.

## ROUTE REVISION — 2026-08-18: the homology detour is unnecessary

Formalising `H₂(SL_n(𝒪), ℤ)` (Hopf's formula, the five-term exact sequence, `K₂(R) = H₂(E(R))`,
homological stability) is **not** required for finite generation of `K₂`.  A purely group-theoretic
argument replaces the whole homological layer.

### The replacement

`K₂(R)` is by definition the kernel of `St(R) → E(R)`, and that kernel is central.  For any central
extension one has the elementary bound:

```text
ψ : F ↠ Ĝ    surjective
π : Ĝ → G    with ker π ≤ Z(Ĝ)
ker (π ∘ ψ) = normalClosure S    with S FINITE
--------------------------------------------------
ker π  is a finitely generated abelian group
```

because `ψ` sends `⁅F, ker(π∘ψ)⁆` to `⁅ψ x, ψ n⁆ = 1`, so `ker π` is a quotient of the relation
module `N/⁅F, N⁆`, which is generated by the images of `S` alone.

Landed unconditionally in `formal/GaloisForLFunctions/HTGeometry/RelationModuleFG.lean`:

```text
normalClosure_eq_closure_sup_commutator   N = ⟪S⟫ ⊔ ⁅F, N⁆
RelationQuotient, relationQuotient_mul_comm       N/⁅F,N⁆ is abelian
relationQuotient_closure_image            it is generated by the image of S
relationQuotient_fg                       finite S ⟹ finitely generated
subgroup_fg_of_commGroup_fg               subgroups of f.g. abelian groups are f.g.
relationQuotient_subgroup_fg              hence every subgroup of the relation module
fg_map_of_central, fg_map_of_le_center    central images are finitely generated
fg_ker_of_central_extension               ** the boxed statement above **
```

### What this leaves as the two real inputs

1. **`St(𝒪)` finitely generated.**  `[DONE]` —
   `formal/GaloisForLFunctions/HTGeometry/SteinbergGroupFiniteGeneration.lean`:

   ```text
   steinbergEntrySubring              the entries whose generators lie in a subgroup form a SUBRING
                                      (additivity gives sums and negatives; the chained commutator
                                       ⁅x_ik(a), x_kj(b)⁆ = x_ij(ab) gives products)
   steinbergGroup_fg                  Subring.closure T = ⊤ with T finite ⟹ St(R) finitely generated
   steinbergGroup_fg_of_moduleFinite  R finitely generated as an abelian group ⟹ St(R) f.g.
                                      — covers every 𝒪_K and every ring of S-integers
   exists_third_index                 3 ≤ card n supplies the spare index
   ```

2. **`E_n(𝒪) = SL_n(𝒪)` finitely presented**, i.e. `ker(F → E(𝒪))` normally generated by finitely
   many elements.  This is the *only* place where the geometry enters, and it is exactly what the
   well-rounded retract delivers: a contractible complex with finitely many cells mod `Γ` and finite
   stabilizers.  Layer F is therefore the whole remaining geometric burden.

Plus, for fixed `n`, the centrality of `K₂` needs the stable range; the corpus proves
`KTwo_mem_center` for elements whose word avoids an index, which is the stable statement.

## RANK 0 WITHOUT BOREL — the analysis-free finish

Finite generation alone gives `K₂(𝒪_S) ≅ ℤ^r ⊕ (finite)`; `r = 0` still needs an input.  It does
**not** have to be Borel's or Garland's analysis:

```text
K₂(𝒪_S) ⊗ ℤ_p ≅ H²_ét(𝒪_S[1/p], ℤ_p(2))          Tate / Merkurjev–Suslin, algebraic
H²_ét(𝒪_S[1/p], ℚ_p(2)) = 0                       Iwasawa's weak Leopoldt for the cyclotomic
                                                   ℤ_p-extension + the global Euler characteristic
--------------------------------------------------
r = 0, i.e. K₂(𝒪_S) ⊗ ℚ = 0
```

The passage from the `p`-adic statement to the rank requires `K₂(𝒪_S)` **finitely generated** — this
is precisely the divisibility firewall (`DivisibilityFirewall.lean`), which shows no amount of
finite-coefficient information can substitute.  So the two halves are:

* geometry of numbers (Layer F) ⟹ finite generation;
* Iwasawa theory ⟹ vanishing rank.

Neither is Borel's analysis.  Borel's theorem remains the target of the user's directive and stays
on the programme, but this route reaches the *card's* requirement without it.

### F3. Generation from a fundamental open set

`formal/GaloisForLFunctions/HTGeometry/GroupActionGeneration.lean`.

```text
meetSet V                 {g | (g • V) ∩ V ≠ ∅}
closure_meetSet_eq_top    ** on a CONNECTED space, an open V whose translates cover generates:
                             ⟪meetSet V⟫ = ⊤ **
```

The proof is the two-open-sets argument: the translates by the generated subgroup form an open set
`A`, the remaining translates an open set `B`; a point of `A ∩ B` exhibits `h⁻¹g ∈ meetSet V`, so
`A ∩ B = ∅`; connectedness and `A ≠ ∅` give `B = ∅`.

Together with proper discontinuity — for compact `K`, only finitely many `g` have `g • K ∩ K ≠ ∅` —
this is the finite-generation half of reduction theory, with **no** simplicial machinery.  The
finite-*presentation* half needs Macbeath's refinement (simple connectivity turns the triple
intersections into a complete set of relations); that is the next target.

### F4. Finite presentability, and the central-kernel theorem

`formal/GaloisForLFunctions/HTGeometry/FinitePresentationIndependence.lean`

```text
map_normalClosure_le            f(⟪S⟫^F) ≤ ⟪f S⟫^H
ker_eq_normalClosure_of_lifts   the abstract core: mutual lifts α, β over the identity of G turn one
                                finite relator set into another
exists_finite_relators          ** B. H. Neumann: finite presentability does not depend on the
                                   chosen finitely generated free presentation **
```

`formal/GaloisForLFunctions/HTGeometry/FinitelyPresentedCentralKernel.lean`

```text
IsFinitelyPresented                          the definition
exists_freeGroup_surjection                  a f.g. group is a quotient of a f.g. free group
Group.fg_of_isFinitelyPresented              FP ⟹ FG
isFinitelyPresented_relators                 relators are finite for EVERY f.g. free presentation
fg_ker_of_central_of_isFinitelyPresented     ** a central extension of a finitely presented group
                                                by a finitely generated group has finitely generated
                                                kernel **
```

With `steinbergGroup_fg_of_moduleFinite` this is the complete reduction:

```text
E_n(𝒪) finitely presented  +  K₂(n, 𝒪) ≤ Z(St_n(𝒪))     ⟹     K₂(n, 𝒪) finitely generated
```

so the two open inputs of Layer F are now exactly:

1. **`E_n(𝒪)` is finitely presented** — Behr's theorem; the reduction-theory burden.
2. **`K₂(n,𝒪)` is central in `St_n(𝒪)`** — the corpus has `KTwo_mem_center` for elements whose word
   avoids an index, which is the *stable* statement; a fixed `n` needs van der Kallen's range, or
   the colimit `St(R) = colim St_n(R)` has to be built.

### F5. The topological input of Macbeath's presentation theorem `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SimplyConnectedCovering.lean` (wired, axiom-clean).

```text
isCoveringMap_injective_of_simplyConnected
    ** a covering map onto a SIMPLY CONNECTED, locally path-connected base, with connected total
       space, is INJECTIVE **
```

The identity of the base lifts to a section `s` (mathlib's
`IsCoveringMap.existsUnique_continuousMap_lifts`), and `s ∘ p` is a lift of `p` through `p` agreeing
with the identity at a point, hence equals the identity by uniqueness of lifts
(`IsCoveringMap.eq_of_comp_eq`).

This is exactly the step of **Macbeath's theorem** where simple connectivity forces the developing
covering to be trivial, so the group presented by the overlaps of a fundamental open set is the
group itself.  What Macbeath still needs is the *construction* of that covering — the quotient
`(Γ̃ × V)/∼` of the presented group times the fundamental open set — and the verification that the
natural map to `X` is a covering map.

### Survey of what mathlib already supplies for this layer

Checked before building, so that nothing is duplicated:

```text
IsCoveringMap, IsCoveringMapOn, IsEvenlyCovered            Topology/Covering/Basic
IsCoveringMap.eq_of_comp_eq                                uniqueness of lifts on a connected domain
IsCoveringMap.exists_path_lifts, liftPath, liftHomotopy    path and homotopy lifting
IsCoveringMap.monodromy, monodromyPerm                     the monodromy action on a fibre
IsCoveringMap.existsUnique_continuousMap_lifts             ** the lifting criterion for a simply
                                                              connected, locally path-connected
                                                              source **
IsQuotientCoveringMap, fiberEquivGroup, toPermFiber        Topology/Covering/Quotient
IsQuotientCoveringMap.fundamentalGroupEquiv                π₁ of the base of a simply connected
                                                           quotient covering ≅ the deck group
Subgroup.fg_of_index_ne_zero                               Schreier's lemma
```

Missing from mathlib and therefore still to be built for this layer: the developing covering of a
group action, Macbeath's presentation theorem itself, Reidemeister–Schreier for *finite
presentability*, and Siegel's finiteness property for the arithmetic action.

### F6. Macbeath's presentation — the group, the surjection, and the criterion `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/MacbeathPresentation.lean` (wired, axiom-clean).

```text
macbeathRels V        the relators s_a · s_b · s_{ab}⁻¹ for triple overlaps V ∩ a·V ∩ ab·V ≠ ∅
MacbeathGroup V       the presented group
macbeathRels_lift     the relators really are relations in the acting group
macbeathHom           ** the canonical homomorphism MacbeathGroup V → G **
macbeathHom_surjective    surjective, by the generation lemma closure_meetSet_eq_top
macbeathRels_finite       finitely many overlaps ⟹ finitely many relators
isFinitelyPresented_macbeathGroup
                      ** finitely many overlaps ⟹ MacbeathGroup V is FINITELY PRESENTED **
meetSet_finite_of_properlyDiscontinuousSMul
                      a properly discontinuous action with a relatively compact fundamental open set
                      has finitely many overlaps
isFinitelyPresented_of_macbeathHom_injective
isFinitelyPresented_of_properlyDiscontinuousSMul
                      ** THE CRITERION: a properly discontinuous cocompact action whose Macbeath
                         homomorphism is injective makes the group finitely presented **
```

The whole finite-presentation layer is now reduced to **one** statement:

> `macbeathHom V` is injective when `X` is simply connected and `V` is connected.

Its proof is the developing covering: build `Y = (MacbeathGroup V × V)/∼` with the quotient
topology, show the natural map `Y → X` is a covering map, and apply
`isCoveringMap_injective_of_simplyConnected` (already proved) — simple connectivity of `X` makes the
covering injective, which is exactly the injectivity of `macbeathHom`.  That construction is the
next brick.

### F7. The developing space of Macbeath's construction `[PROVED so far]`

`formal/GaloisForLFunctions/HTGeometry/MacbeathDevelopingSpace.lean` (wired, axiom-clean).

```text
macbeathOf                a generator of Macbeath's group (added to MacbeathPresentation)
DevSheet V                one copy of V for each element of Macbeath's group — the SIGMA type, so
                          that the sheet index is automatically discrete
DevRel V                  ** the gluing move: the copy at g is glued to the copy at g·s_γ along the
                             overlap, by x ↦ γ⁻¹·x **
DevSpace V                the developed space, as a Quot of the gluing relation
devSheetMap, devSheetMap_respects, devMap
                          ** the map to X, [g, x] ↦ macbeathHom g · x **
continuous_devMap         continuous
devMap_surjective         surjective, since the translates of V cover
devSmul, devSmul_one, devSmul_mul, continuous_devSmul
                          ** Macbeath's group acts on the developed space by left multiplication on
                             the sheet index **
devMap_devSmul            ** the map to X is EQUIVARIANT through macbeathHom **
```

The topology on the sheets is handled by taking a **sigma type** rather than a product with a
discrete group, so no topology has to be put on `MacbeathGroup V` at all.

What remains for Macbeath's theorem is the local structure: that `devMap` is a covering map, with the
explicit description of `devMap ⁻¹' (γ·V)` as a disjoint union of sheets.  Injectivity of
`macbeathHom` then follows by reading off the fibre, using
`isCoveringMap_injective_of_simplyConnected`.

### F8. The gluing relation is ALREADY an equivalence, and Macbeath modulo the covering property `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/MacbeathPresentation.lean` (extended) and
`formal/GaloisForLFunctions/HTGeometry/MacbeathOneStep.lean` (wired, axiom-clean).

```text
inv_mem_meetSet     the overlap set is symmetric
macbeathOf_mul      ** s_γ · s_δ = s_{γδ} ** under the triple-overlap hypothesis
macbeathOf_one      ** s_1 = 1 **
macbeathOf_inv      ** s_{γ⁻¹} = s_γ⁻¹ **

DevOneStep V        the ONE-STEP relation: q is p moved by a single γ ∈ S
devRel_le_devOneStep
devOneStep_refl / _symm / _trans      reflexivity is s_1 = 1, symmetry is s_{γ⁻¹} = s_γ⁻¹, and
                                      TRANSITIVITY IS EXACTLY MACBEATH'S RELATION — the common
                                      point of the two moves supplies the triple overlap
devOneStep_equivalence                ** the one-step relation is an equivalence relation **
devSpace_mk_eq_iff                    ** two sheets have the same class exactly when a SINGLE group
                                         element relates them **

macbeathHom_injective_of_devMap_injective
                    ** injectivity of the developing map forces injectivity of macbeathHom **:
                    a g in the kernel has its sheet glued to the identity sheet, so g = s_γ⁻¹ with
                    γ⁻¹ = macbeathHom g = 1, whence g = s_1 = 1
macbeathHom_injective_of_isCoveringMap
                    ** MACBEATH'S THEOREM, modulo the covering property **
```

The structural point is `devSpace_mk_eq_iff`: the gluing relation does not need its transitive
closure, because Macbeath's defining relations are exactly what makes one-step composition work.
This is what turns the developed space into something whose points can be read off.

**What is left for the whole finite-presentation layer**: that `devMap` is a covering map, and that
the developed space is connected.  Everything else — generation, the presentation, finiteness of the
presentation, the developing space, the action, the one-step description, the transfer of
injectivity, and the simply-connected covering theorem — is formal and unconditional.

### F9. The sheets of the developing space `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/MacbeathSheets.lean` (wired, axiom-clean).

```text
devSpace_mk_eq_mk_of_macbeathHom_eq
      ** sheets with the same image under macbeathHom SEPARATE POINTS **: if [h,y] = [h',y'] and
         macbeathHom h = macbeathHom h', then h = h' and y = y' — because the connecting γ satisfies
         macbeathHom h · γ = macbeathHom h', so γ = 1 and s_1 = 1
sheetImage V h O
      the image in the developed space of a subset of V, on the sheet at h
preimage_sheetImage
      its Quot-preimage, computed from the one-step description
isOpen_sheetImage
      ** the image of an OPEN subset of V on a sheet is OPEN ** — the preimage is, on each sheet
         index, a union over γ of the preimages of O ∩ V under x ↦ γ⁻¹·x, and those are open
         because the action is by homeomorphisms
```

With these, the even covering of `macbeathHom(h₀) · V` is completely described: the preimage is the
disjoint union of the sheets at the `h` with `macbeathHom h = macbeathHom h₀`, each sheet is open,
each is mapped bijectively and openly onto the base set, and the sheets are pairwise disjoint.  The
only remaining step of the covering property is packaging that data into a `Trivialization`.
