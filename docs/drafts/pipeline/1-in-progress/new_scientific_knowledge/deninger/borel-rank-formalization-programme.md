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

### F10. THE DEVELOPING MAP IS A COVERING MAP `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/MacbeathQuotientMap.lean` and
`formal/GaloisForLFunctions/HTGeometry/MacbeathCovering.lean` (wired, axiom-clean).

```text
sheetTrace, isOpen_sheetTrace       the trace of an open set on a sheet is open
isOpenMap_devMap                    ** the developing map is OPEN ** — an open set is, on each
                                       sheet, an open subset of V, and its image is the translate
isQuotientMap_devMap                hence a quotient map

devKerMulAction                     ** the kernel of macbeathHom acts on the developed space **
devKerContinuousConstSMul           continuously
devMap_eq_iff_mem_orbit             ** THE FIBRES ARE THE ORBITS ** — given two sheets with the same
                                       image, the connecting γ = φ(q)⁻¹φ(p) lies in the overlap set,
                                       and φ(p)·(q·s_γ)⁻¹ lies in the kernel and carries one to the
                                       other
isQuotientCoveringMap_devMap        ** a QUOTIENT COVERING MAP **: the disjointness neighbourhood of
                                       a point is its own sheet, by the separation lemma
isCoveringMap_devMap                ** THE DEVELOPING MAP IS A COVERING MAP **
```

The route avoids building a `Trivialization` by hand: mathlib's `IsQuotientCoveringMap` turns the
three conditions — quotient map, fibres = orbits, disjoint translates of a neighbourhood — into the
covering property, and all three are exactly what the sheet analysis provides.

**Only one statement of the whole finite-presentation layer is now open**: the developed space is
connected.  Its proof is the chain of sheets — each sheet is a continuous image of the connected `V`,
the sheets at `g` and `g·s_γ` always meet, and the `s_γ` generate Macbeath's group.

### F11. MACBEATH'S THEOREM IS PROVED `[COMPLETE]`

`formal/GaloisForLFunctions/HTGeometry/MacbeathConnected.lean` (wired, axiom-clean).

```text
sheetImage_self_eq_range, isPreconnected_sheet
      a sheet is the continuous image of V, hence connected
preconnectedSpace_devSpace
      ** THE DEVELOPED SPACE IS CONNECTED ** — the elements whose sheet lies in the component of the
      base point form a SUBGROUP (via the "right translation preserves the property" trick), it
      contains every generator because the sheets at g and g·s_γ share a point of V ∩ γ·V, and the
      generators generate
macbeathHom_injective
      ** MACBEATH'S THEOREM: for a group acting on a simply connected, locally path-connected space
         with a connected fundamental open set, the overlaps PRESENT the group **
isFinitelyPresented_of_macbeath
      ** a group acting properly discontinuously and cocompactly on a simply connected, locally
         path-connected space, with a connected fundamental open set, is FINITELY PRESENTED **
```

The finite-presentation criterion is therefore **complete and unconditional**:

```text
closure_meetSet_eq_top                  generation
MacbeathGroup, macbeathHom              the presentation and the surjection
isFinitelyPresented_macbeathGroup       finitely many overlaps ⟹ finitely presented
DevSpace, devMap, devSmul               the developing space, its map, the action
devSpace_mk_eq_iff                      the gluing relation is already one step
devSpace_mk_eq_mk_of_macbeathHom_eq     sheets separate points
isOpen_sheetImage, isOpenMap_devMap     the sheets are open, the map is open
devMap_eq_iff_mem_orbit                 the fibres are the orbits of ker macbeathHom
isCoveringMap_devMap                    ** the developing map is a covering map **
preconnectedSpace_devSpace              ** the developed space is connected **
isCoveringMap_injective_of_simplyConnected   simple connectivity trivialises the covering
macbeathHom_injective                   ** MACBEATH'S THEOREM **
isFinitelyPresented_of_macbeath         ** the criterion **
```

What the arithmetic application still needs from outside this layer: Siegel's finiteness property
(to supply a fundamental open set with finitely many overlaps for `SL_n(𝒪)`) and simple connectivity
of the symmetric space.

### F12. Macbeath's criterion on a convex domain — the shape arithmetic groups need `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/MacbeathConvexDomain.lean` (wired, axiom-clean).

```text
simplyConnectedSpace_of_convex        an open convex set is contractible, hence simply connected
locallyPathConnectedSpace_of_isOpen   an open subset of a locally path-connected space is locally
                                      path connected
connectedSpace_of_convex              and connected
isFinitelyPresented_of_macbeath_convex
      ** A GROUP ACTING ON A NONEMPTY OPEN CONVEX SET, WITH A CONNECTED FUNDAMENTAL OPEN SET WHOSE
         OVERLAP SET IS FINITE, IS FINITELY PRESENTED **
```

This is exactly the shape the arithmetic case needs: the space of positive definite forms is an
**open convex cone**, and the fundamental open set is a Siegel set.  Note that the criterion asks
only for the overlap set to be *finite* — not for the action to be cocompact — which is what makes
it applicable to the **non-uniform** lattice `SL_n(𝒪)`, where Siegel's finiteness property provides
exactly that.

The two arithmetic inputs that remain for `E_n(𝒪)` finitely presented are therefore:

1. the action of `SL_n(𝒪)` on the positive definite cone, with a Siegel set as fundamental open set
   (`⋃ γ • V = X`);
2. **Siegel's finiteness property**: `{γ : γ·V ∩ V ≠ ∅}` is finite.

Nothing else in the finite-presentation layer is open.

### F13. The positive definite cone is an open convex set `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/PositiveDefiniteCone.lean` (wired, axiom-clean).

```text
symmMatrices n              the real symmetric matrices, as a SUBMODULE (so a topological vector
                            space, which is where the convexity has to live — the positive definite
                            set is NOT open in all of Matrix, since being symmetric is closed)
isHermitian_of_mem_symmMatrices
posDefCone n                the positive definite ones inside it
posDefCone_nonempty         the identity matrix
convex_posDefCone           ** CONVEX **
posDef_iff_sphere           positive definiteness of a symmetric matrix is a condition on the unit
                            sphere
isOpen_posDefCone           ** OPEN ** — the matrices failing positivity somewhere on the sphere are
                            the image under the projection `Matrix × sphere → Matrix` of a closed
                            set, and that projection is closed because the sphere is compact
```

Combined with `isFinitelyPresented_of_macbeath_convex`, the topological side of the arithmetic
application is **complete**: the space is an open convex set, so simple connectivity, local path
connectivity and connectivity all come for free.

The remaining arithmetic inputs are exactly:

1. the action of `SL_n(𝒪)` on `posDefCone`, with a Siegel set `V` satisfying `⋃ γ • V = X`;
2. **Siegel's finiteness property**: `{γ : γ·V ∩ V ≠ ∅}` is finite.

### F14. `SL(n, ℤ)` acts on the cone, and the criterion is now ONE reduction-theory input away `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/PositiveDefiniteConeAction.lean` (wired, axiom-clean).

```text
slReal                    an integral unimodular matrix, read over ℝ
slReal_one, slReal_mul, slReal_det, slReal_isUnit, slReal_vecMul_injective
symmConj                  the congruence action A ↦ g·A·gᵀ on symmetric matrices
symmConj_one, symmConj_mul
symmConj_posDef           ** congruence by an invertible matrix preserves positive definiteness **
posDefConeMulAction       ** the MulAction of SL(n, ℤ) on the positive definite cone **
posDefConeContinuousConstSMul
locallyPathConnectedSpace_symmMatrices
                          the symmetric matrices are locally path connected — via the defeq between
                          `Submodule ℝ (Matrix …)` and `Submodule ℝ (Fin n → Fin n → ℝ)`, which
                          makes the Pi normed-space instances apply
isFinitelyPresented_specialLinearGroup_of_siegel
                          ** SL(n, ℤ) IS FINITELY PRESENTED as soon as reduction theory supplies a
                             connected fundamental open set with finitely many overlaps **
```

Every topological hypothesis is discharged: the cone is open and convex, so simple connectivity,
local path connectivity and connectivity are automatic, and the action is by congruence.

**The finite-generation half of the card is now ONE named classical theorem away**:

> **Siegel's finiteness property.**  There is a connected open `V` in the positive definite cone with
> `⋃_{γ ∈ SL(n, ℤ)} γ·V = X` and `{γ : γ·V ∩ V ≠ ∅}` finite.

Given it, `isFinitelyPresented_specialLinearGroup_of_siegel` gives `SL(n, ℤ)` finitely presented;
with `steinbergGroup_fg_of_moduleFinite` and `fg_ker_of_central_of_isFinitelyPresented` that gives
`K₂` finitely generated.  The rank-zero half (Borel, or Tate + Iwasawa) is independent of this
layer.

### F15. `SL(n, ℤ)` acts PROPERLY DISCONTINUOUSLY on the cone `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/PositiveDefiniteBounds.lean` (wired, axiom-clean).

```text
quadForm, continuous_quadForm, quadForm_pos
exists_lower_bound_of_isCompact    ** a POSITIVE uniform lower bound on a compact family of forms **
exists_upper_bound_of_isCompact    a uniform upper bound
quadForm_smul, quadForm_zero, quadForm_ge_of_sphere_bound
quadForm_smul_group                ** the congruence formula: Q_{g·A}(x) = Q_A(gᵀx) **
norm_single_one
entry_bound                        ** a group element carrying one compact family of forms into
                                      another has BOUNDED ENTRIES ** — from m‖gᵀx‖² ≤ Q_A(gᵀx)
                                      = Q_{g·A}(x) ≤ M on the unit sphere
finite_entries_bounded             finitely many integer matrices with bounded entries
finite_meet_of_isCompact           ** {γ : γ·K ∩ L ≠ ∅} is FINITE for K, L compact **
properlyDiscontinuousSMul_posDefCone
                                   ** THE ACTION IS PROPERLY DISCONTINUOUS **
```

This is the properness half of reduction theory, proved from scratch: compactness gives uniform
bounds on the quadratic form, the bounds give bounded entries, and integrality gives finiteness.

What is still missing for `SL(n, ℤ)` finitely presented is only the *fundamental set*: a connected
open `V` with `⋃ γ·V = X`.  Given such a `V` with relatively compact closure the overlap set is
finite by `meetSet_finite_of_properlyDiscontinuousSMul` — but the action is not cocompact, so what
is needed is a Siegel set together with Siegel's finiteness property, of which the properness proved
here is the first half.

### F16. The arithmetic minimum of a positive definite form `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/ArithmeticMinimum.lean` (wired, axiom-clean).

```text
intVec, intVec_injective, intVec_eq_zero_iff    an integer vector read over ℝ
finite_intVec_bounded         finitely many integer vectors with bounded entries
finite_latticePoints_le       ** finitely many integer vectors take a bounded value ** — the form
                              dominates m‖v‖², so a bound on the value bounds the entries
exists_arithmeticMinimum      ** THE MINIMUM OVER NONZERO INTEGER VECTORS IS ATTAINED **
```

This is the first step of Minkowski reduction: reduction proceeds by repeatedly choosing vectors
that realise the minimum, and the properness proved here is what makes those choices possible.

### State of the finite-generation half

```text
St(𝒪) finitely generated                                   [PROVED]
central extension ⟹ K₂ finitely generated                  [PROVED]
Macbeath's criterion (open convex domain)                   [PROVED]
the positive definite cone is open and convex               [PROVED]
SL(n, ℤ) acts on it, continuously                           [PROVED]
the action is properly discontinuous                        [PROVED]
the arithmetic minimum is attained                          [PROVED]
--------------------------------------------------------------------
a fundamental open set with finitely many overlaps          [OPEN: Siegel]
```

## F17. Jacobi coordinates — 2026-08-19 `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/JacobiDecomposition.lean`

- `blockTriangular_of_lower`, `lower_of_blockTriangular`, `lower_mul_diag` — the triangularity
  bookkeeping in the form mathlib's `Matrix.BlockTriangular` takes.
- `lowerTriangular_diag_ne_zero` — an invertible lower triangular matrix has nonzero diagonal.
- `unitTriangular_inv_diag` — the inverse of a unit lower triangular matrix has unit diagonal.
- **`exists_jacobi_decomposition`** — every real positive definite `A` is `Uᵀ D U` with `U`
  unipotent upper triangular and `D` positive diagonal.  Built from mathlib's `LDL` (Gram–Schmidt in
  the inner product of the form), normalised so the diagonal is one and inverted.
- **`quadForm_jacobi`** — `A[v] = ∑ dᵢ (Uv)ᵢ²`.

These are the coordinates in which Siegel sets are defined, so this is the first step of the
reduction theory that `isFinitelyPresented_of_macbeath_convex` is waiting for.  The remaining steps:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set 𝔖_{t,u} as explicit inequalities        [next]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [next]
SL(n,ℤ)·𝔖 = X  (reduction)                            [OPEN]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

## F18. Siegel sets and quasi-diagonality `[PROVED]`

- `UnipotentInverseBound.lean` — `unipotentBall` (unipotent upper triangular with entries bounded
  by `u`), `det_eq_one_of_unipotent`, `inv_eq_adjugate_of_unipotent`,
  **`isCompact_unipotentBall`**, **`exists_unipotent_inv_bound`**: the inverses are uniformly
  bounded.  The determinant is identically one on the ball, so the inverse is the adjugate — a
  polynomial in the entries — and the ball is a closed subset of a box, hence compact.

- `SiegelSet.lean` — `JacobiData` (the pair `(U, d)`), `JacobiData.form`, `exists_jacobiData`,
  `JacobiData.IsSiegel` (the two Siegel bounds: `dᵢ ≤ t·dᵢ₊₁` and `|Uᵢⱼ| ≤ u`),
  **`JacobiData.d_le_pow`**, `d_le_pow_of_le`, **`d_le_pow_n`**: the diagonal bound iterated along
  a chain, so `dᵢ ≤ tⁿ dⱼ` whenever `i ≤ j`.

- `SiegelQuasiDiagonal.lean` — `JacobiData.det_eq_one`, `JacobiData.inv_upper`,
  `JacobiData.mulVec_inv`, `JacobiData.quadForm_eq`, and **`exists_quasiDiagonal`**:

  > for every `n, t ≥ 1, u` there is `c > 0` with `A[v] ≥ c · ∑ dᵢ vᵢ²` for every form in the
  > Siegel set and every `v`.

  Both Siegel bounds enter exactly once: the unipotent bound through the uniform bound on `U⁻¹`,
  and the diagonal bound through `dᵢ ≤ tⁿ dⱼ` — which is applied only for `i ≤ j`, precisely the
  range in which the entries of `U⁻¹` can be nonzero.

Updated state of the reduction-theory lane:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set as explicit inequalities                [PROVED]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [PROVED]
SL(n,ℤ)·𝔖 = X  (reduction)                            [OPEN]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

Quasi-diagonality already gives one half of Siegel's finiteness: if `A` and `γᵀAγ` both lie in the
Siegel set then `dₖ γₖᵢ² ≤ K d'ᵢ` for all `k, i`, so a nonzero *integer* entry forces
`dₖ ≤ K d'ᵢ`.  What remains is the combinatorial step that turns those support constraints into a
bound on the entries themselves, using `∏ dᵢ = ∏ d'ᵢ = det A`.

## F19. Size reduction `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelSizeReduction.lean`

- `IsUnipotentUpper`, `IsIntUnipotent`, with `upper_mul_diag`, `IsUnipotentUpper.mul`,
  `IsIntUnipotent.mul`, `isIntUnipotent_one` — the real and integral unipotent upper triangular
  matrices are closed under products.
- `SizeReduced k` — the superdiagonals of offset at most `k` lie in `[-1/2, 1/2]`.
- **`exists_sweep`** — one integral shear at offset `k+1` reduces that superdiagonal and leaves the
  smaller offsets untouched.  The shear `1 + E` has `E` supported on a single offset, so
  `(V·E)ᵢⱼ` vanishes for every smaller offset (the surviving index would sit strictly left of `i`,
  where `V` is zero) and equals `eᵢ` on offset `k+1` (where the surviving index is `i` itself and
  `Vᵢᵢ = 1`).  Choosing `eᵢ = −round(Vᵢ,ᵢ₊ₖ₊₁)` finishes.
- **`exists_size_reduction`** — sweeping the offsets outwards, every unipotent upper triangular
  matrix becomes size reduced after multiplication by an integral one.
- `JacobiData.shear`, `shear_d`, `shear_U`, **`shear_form`** (`γᵀAγ`), **`exists_sizeReduced_shear`**
  — an integral unipotent basis change is a congruence of the form that leaves the Jacobi diagonal
  fixed, so every form has a size reduced Jacobi datum in its orbit, with the same diagonal.

Updated state of the reduction-theory lane:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set as explicit inequalities                [PROVED]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [PROVED]
size reduction: |Uᵢⱼ| ≤ 1/2 after an integral shear    [PROVED]
the Lovász swap: dᵢ ≤ t dᵢ₊₁ after a transposition     [next]
SL(n,ℤ)·𝔖 = X  (reduction)                            [OPEN]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

The covering statement now needs only the second Siegel bound.  The LLL route supplies it: a
transposition of two adjacent basis vectors replaces `(dᵢ, dᵢ₊₁)` by
`(dᵢ₊₁ + u² dᵢ, dᵢ dᵢ₊₁ / (dᵢ₊₁ + u² dᵢ))`, which strictly lowers `dᵢ` whenever
`dᵢ₊₁ < (1 − u²) dᵢ`; with `|u| ≤ 1/2` from size reduction this is implied by `dᵢ₊₁ < (3/4) dᵢ`.
Minimising the potential `∏ dᵢ^(n−i)` over the orbit therefore forces `dᵢ ≤ (4/3) dᵢ₊₁`.

## F20. Leading minors and uniqueness of the Jacobi diagonal `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/JacobiLeadingMinors.lean`

- `leadingBlock`, `leadingBlock_upper`, `leadingBlock_unit`.
- **`leadingBlock_congr`** — the leading `k × k` block of `Uᵀ D U` is `Uₖᵀ Dₖ Uₖ`.  An upper
  triangular `U` has nothing below the diagonal to couple the block to the rest: in the entry sum,
  every index outside the block sits strictly to the right of the row index, where `U` vanishes.
- **`det_leadingBlock_form`** — hence `det Aₖ = ∏_{m<k} dₘ`, since the leading block of `U` is again
  unipotent so has determinant one.
- **`JacobiData.d_unique`** — the Jacobi diagonal is determined by the form, via
  `dₖ = det Aₖ₊₁ / det Aₖ`.

This makes the reduction-theory potential `∏ₖ det Aₖ` a function of the *form* rather than of a
chosen decomposition, which is what lets the LLL minimisation argument be stated at all: a swap of
two adjacent basis vectors changes exactly one leading minor, so the potential is a well-defined
quantity to minimise over the `SL(n, ℤ)`-orbit.

Updated state of the reduction-theory lane:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set as explicit inequalities                [PROVED]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [PROVED]
size reduction: |Uᵢⱼ| ≤ 1/2 after an integral shear    [PROVED]
uniqueness of the diagonal; the potential ∏ det Aₖ     [PROVED]
the Lovász swap: dᵢ ≤ t dᵢ₊₁ after a transposition     [next]
SL(n,ℤ)·𝔖 = X  (reduction)                            [OPEN]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

## F21. The Lovász bound from local minimality `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelLovasz.lean`

- **`JacobiData.form_diag`** — `A_jj = ∑ₘ dₘ Uₘⱼ²`: the diagonal entries read off the Jacobi
  coordinates.
- `JacobiData.d_le_form_diag` — hence `dⱼ ≤ A_jj`.
- **`JacobiData.form_diag_le`** — on a size reduced datum, `A_jj ≤ dⱼ + ¼ ∑_{m<j} dₘ`.
- **`lovasz_of_le`** — if `dₖ ≤ d_l + U_kl² dₖ` for some `l > k` on a size reduced datum, then
  `dₖ ≤ (4/3) d_l`.

This settles the *shape* of the second Siegel bound and, importantly, which route can supply it.
Minkowski reduction cannot: the naive induction gives `dₖ ≤ dₖ₊₁ + ¼ ∑_{m≤k} dₘ`, whose constant
grows with `k` and breaks once the accumulated sum exceeds `4 dₖ`.  The local condition above has no
such defect — `4/3` is uniform in `k` and in `n` — because it compares `dₖ` only against the squared
distance of the *next* basis vector from the earlier ones, never against the whole prefix.

What `lovasz_of_le` still needs as input is exactly that geometric minimality, `dₖ ≤ dₖ₊₁ + u² dₖ`.
For `k = 0` it is the arithmetic minimum (`exists_arithmeticMinimum`, F16), since
`A_{11} = d₁ + u² d₀` is the value of the form at the second basis vector.  For general `k` it is
minimality of `dₖ` against lattice vectors outside the span of the first `k−1` basis vectors, which
is the greedy construction of the basis — the remaining open step.

Updated state of the reduction-theory lane:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set as explicit inequalities                [PROVED]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [PROVED]
size reduction: |Uᵢⱼ| ≤ 1/2 after an integral shear    [PROVED]
uniqueness of the diagonal; the potential ∏ det Aₖ     [PROVED]
the Lovász bound dₖ ≤ (4/3) dₖ₊₁ from local minimality [PROVED]
the greedy basis realising that minimality             [next]
SL(n,ℤ)·𝔖 = X  (reduction)                            [OPEN]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

## F22. The first Lovász bound, closed `[PROVED]`

Appended to `formal/GaloisForLFunctions/HTGeometry/SiegelLovasz.lean`:

- `JacobiData.form_diag_zero` — `A₀₀ = d₀`.
- **`JacobiData.form_diag_succ`** — when the coordinates before `i` vanish,
  `A_jj = dᵢ Uᵢⱼ² + dⱼ` for `j` the successor of `i`.  This is the squared distance of the next
  basis vector from the earlier ones, written out.
- **`JacobiData.lovasz_succ`** — hence `dᵢ ≤ (4/3) dⱼ` whenever `dᵢ ≤ A_jj`.
- **`JacobiData.lovasz_first`** — the case `i = 0`, where the hypothesis on earlier coordinates is
  vacuous.
- `quadForm_single` — the value of the form at a standard basis vector is the diagonal entry.
- **`lovasz_first_of_arithmeticMinimum`** — **the first Lovász bound is now unconditional**: if the
  first standard basis vector realises the arithmetic minimum of the form, then `d₀ ≤ (4/3) d₁`.

This closes the bottom step of the second Siegel bound outright, with `exists_arithmeticMinimum`
(F16) supplying the minimality.  The general step needs the same inequality one level up: minimality
of `dₖ` against lattice vectors outside the span of the first `k−1` basis vectors.  That is the
greedy basis construction, and `lovasz_succ` is stated exactly so that it plugs in — its hypothesis
`hpre` is precisely "the new vector has no component along the earlier basis vectors", which the
greedy choice provides.

Updated state of the reduction-theory lane:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set as explicit inequalities                [PROVED]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [PROVED]
size reduction: |Uᵢⱼ| ≤ 1/2 after an integral shear    [PROVED]
uniqueness of the diagonal; the potential ∏ det Aₖ     [PROVED]
the Lovász bound from local minimality                 [PROVED]
the first Lovász bound d₀ ≤ (4/3) d₁                   [PROVED]
the greedy basis: minimality at every level            [next]
SL(n,ℤ)·𝔖 = X  (reduction)                            [OPEN]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

## F23. The projected norm; the Siegel conditions reduced to a greedy basis `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelProjectedNorm.lean`

- **`JacobiData.projNorm`** — `projNorm i v = ∑_{m ≥ i} dₘ (Uv)ₘ²`, the squared norm of the
  projection of `v` orthogonally to the first `i` Jacobi directions; `projNorm_nonneg`,
  `projNorm_le` (it is at most the value of the form).
- **`projNorm_self`** — `projNorm i eᵢ = dᵢ`.
- **`projNorm_succ`** — `projNorm i eⱼ = dᵢ Uᵢⱼ² + dⱼ` for `j` the successor of `i`.
- **`lovasz_of_projNorm_min`** — hence greedy minimality at level `i` gives `dᵢ ≤ (4/3) dⱼ`.
- **`JacobiData.isSiegel_of_greedy`** — **a greedy, size reduced Jacobi datum satisfies
  `IsSiegel (4/3) 1`**: both Siegel bounds, with explicit parameters.

This corrects the hypothesis shape recorded in F22.  There, `lovasz_succ` demanded that the later
basis vector have *no* component along the earlier ones (`hpre`).  That is unachievable: a greedy
lift is only ever determined modulo the earlier basis vectors, so its real coordinates cannot be
made to vanish — size reduction brings them into `[-1/2, 1/2]` and no further.  Projecting them away
instead is both correct and exactly what the greedy minimum is a minimum *of*.  `lovasz_of_le`
(F21) was already stated in the right generality and is unaffected.

Updated state of the reduction-theory lane:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set as explicit inequalities                [PROVED]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [PROVED]
size reduction: |Uᵢⱼ| ≤ 1/2 after an integral shear    [PROVED]
uniqueness of the diagonal; the potential ∏ det Aₖ     [PROVED]
the Lovász bound from local minimality                 [PROVED]
the first Lovász bound d₀ ≤ (4/3) d₁                   [PROVED]
greedy + size reduced ⟹ IsSiegel (4/3) 1              [PROVED]
the greedy basis itself                                [next]
SL(n,ℤ)·𝔖 = X  (reduction)                            [OPEN]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

The covering statement is now exactly one construction away: a `ℤ`-basis whose `i`-th vector
minimises `projNorm i` among lattice vectors of nonzero projection.  Discreteness supplies each
individual minimum (`finite_latticePoints_le`, F16); what remains is that the minimising vectors can
be chosen to form a basis, i.e. that a vector realising the projected minimum is primitive modulo
the earlier ones.

## F24. Minimisers of the projected norm have primitive tail `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelGreedyPrimitive.lean`

- **`JacobiData.projNorm_smul`** — the projected norm is quadratically homogeneous.
- **`JacobiData.projNorm_congr_tail`** — it depends only on the coordinates from `i` on.  (`U` is
  upper triangular, so `(Uv)ₘ` for `m ≥ i` involves no coordinate before `m`.)
- **`JacobiData.not_dvd_of_projNorm_min`** — **a lattice vector realising the minimum of the
  projected norm at level `i` has no common divisor `k ≥ 2` among its coordinates from `i` on.**
  Dividing by `k` would keep the projection nonzero and divide the projected norm by `k²`.

This is the step that makes the greedy construction produce a **basis** rather than merely a
sequence of short vectors: primitivity modulo the earlier coordinates is exactly the condition under
which the minimiser extends the partial basis.

Updated state of the reduction-theory lane:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set as explicit inequalities                [PROVED]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [PROVED]
size reduction: |Uᵢⱼ| ≤ 1/2 after an integral shear    [PROVED]
uniqueness of the diagonal; the potential ∏ det Aₖ     [PROVED]
the Lovász bound from local minimality                 [PROVED]
greedy + size reduced ⟹ IsSiegel (4/3) 1              [PROVED]
minimisers have primitive tail                         [PROVED]
primitive tail ⟹ extends the partial basis            [next]
SL(n,ℤ)·𝔖 = X  (reduction)                            [OPEN]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

The remaining step of the covering is now purely module-theoretic and carries no analysis: a vector
of `ℤⁿ` whose coordinates from `i` on are setwise coprime extends the first `i` standard basis
vectors to a basis of `ℤⁿ`.  Equivalently, a primitive vector of `ℤ^{n-i}` is the first column of a
matrix of `SL(n-i, ℤ)`.

## F25. The Siegel entry bound `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelEntryBound.lean`

- **`congr_diag_eq_quadForm_col`** — the `i`-th diagonal entry of `γᵀAγ` is the value of `A` at the
  `i`-th column of `γ`.
- **`JacobiData.form_diag_le_pow`** — on a Siegel set, `A_ii ≤ (1 + n tⁿ/4) dᵢ`: the earlier
  diagonal entries entering `A_ii` are each at most `tⁿ dᵢ`, and size reduction weights them by at
  most a quarter.
- **`siegel_entry_bound`** — **if a form and its congruate by `γ` both lie in a Siegel set then
  `c · dₖ γₖᵢ² ≤ (1 + n tⁿ/4) d'ᵢ` for every `k, i`.**

This is the entire analytic content of Siegel's finiteness property, and it now rests only on
results already proved: quasi-diagonality (F18) for the lower bound, and the two Siegel bounds
(F18, F19) for the upper one.

What remains for finiteness is arithmetic, not analysis.  The entries of `γ` are integers, so
`γₖᵢ ≠ 0` forces `|γₖᵢ| ≥ 1` and hence `dₖ ≤ K d'ᵢ`; the support pattern of `γ` is therefore
constrained by the ratios `d'ᵢ / dₖ`.  Turning those constraints into a bound on the entries uses
`∏ dᵢ = ∏ d'ᵢ = det A` (available from F20) together with a decomposition of `γ`; the naive
argument through the permutation supplied by `det γ ≠ 0` bounds only `d_{σ(i)} / d'ᵢ`, not
`dₖ / d'ᵢ` for arbitrary `k`, so a finer argument is needed there.

Updated state of the reduction-theory lane:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set as explicit inequalities                [PROVED]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [PROVED]
size reduction: |Uᵢⱼ| ≤ 1/2 after an integral shear    [PROVED]
uniqueness of the diagonal; the potential ∏ det Aₖ     [PROVED]
the Lovász bound from local minimality                 [PROVED]
greedy + size reduced ⟹ IsSiegel (4/3) 1              [PROVED]
minimisers have primitive tail                         [PROVED]
the Siegel entry bound c dₖ γₖᵢ² ≤ K d'ᵢ              [PROVED]
primitive tail ⟹ extends the partial basis            [OPEN, module theory]
the arithmetic step of Siegel finiteness               [OPEN]
```

## F26. The projected norm is a squared distance `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelProjIntrinsic.lean`

- `lowerSupport` — the vectors supported on the coordinates before `i`, as a submodule.
- `JacobiData.mulVec_lower` — an upper triangular `U` preserves that support condition.
- **`JacobiData.projNorm_le_form_sub`** — `projNorm i v ≤ A[v − w]` for every `w` supported
  below `i`.
- **`JacobiData.eq_zero_of_mulVec_lower`** — the transform is injective on `lowerSupport i`; proved
  by back-substitution, as a downward induction on `i − p`.
- `JacobiData.lowerMap`, `lowerMap_injective`, **`JacobiData.exists_proj`** — injectivity in equal
  finite dimension gives surjectivity, hence the projection exists.
- **`JacobiData.projNorm_eq_form_sub`** — **`projNorm i v` is exactly the squared distance of `v`
  from the span of the first `i` coordinates.**

This makes `projNorm` *intrinsic*: it depends only on the form and on the span of the first `i`
basis vectors, not on the basis chosen inside that span.  That is precisely what the Lovász swap
needs and what removes the determinant computation that blocked it.  Transposing two adjacent basis
vectors leaves the span of the earlier ones unchanged, so the new `i`-th Jacobi entry is the *old*
projected norm of the transposed vector — which `projNorm_succ` (F23) already evaluates as
`dᵢ Uᵢⱼ² + dⱼ`.  No Cauchy–Binet, no minor determinant, no explicit re-triangularisation.

Updated state of the reduction-theory lane:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set as explicit inequalities                [PROVED]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [PROVED]
size reduction: |Uᵢⱼ| ≤ 1/2 after an integral shear    [PROVED]
uniqueness of the diagonal; the potential ∏ det Aₖ     [PROVED]
the Lovász bound from local minimality                 [PROVED]
greedy + size reduced ⟹ IsSiegel (4/3) 1              [PROVED]
minimisers have primitive tail                         [PROVED]
the Siegel entry bound c dₖ γₖᵢ² ≤ K d'ᵢ              [PROVED]
projNorm is intrinsic (a squared distance)             [PROVED]
the swap identity d'ᵢ = dᵢ₊₁ + u² dᵢ                   [next, now unblocked]
SL(n,ℤ)·𝔖 = X  (reduction)                            [OPEN]
the arithmetic step of Siegel finiteness               [OPEN]
```

## F27. The Lovász swap identity `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelSwap.lean`

- **`quadForm_congr`** — the value of a congruate at `x` is the value of the form at the transported
  vector.
- `permMatrix`, `permMatrix_mulVec`, `permMatrix_involutive`, `permMatrix_single_swap`,
  `permMatrix_lowerSupport` — the permutation matrix, its action, and the two facts the swap needs:
  it exchanges the two basis vectors and preserves the support condition below `i` (both swapped
  indices being at least `i`).
- **`swap_d_eq_projNorm`** — **if `J'` is Jacobi data for the form obtained by transposing the basis
  vectors `i` and `j`, then `d'ᵢ = projNorm i e_j` for the original data.**  Both inequalities come
  from the two halves of the intrinsic characterisation (F26), transported through the permutation:
  a competitor for one side maps to a competitor for the other.
- **`swap_d_lt`** — **a swap strictly lowers `dᵢ` exactly when the Lovász condition fails**, i.e.
  when `dⱼ < (3/4) dᵢ` on a size reduced datum.

Combined with `projNorm_succ` (F23), this evaluates the swap: `d'ᵢ = dᵢ Uᵢⱼ² + dⱼ`.  It required
neither Cauchy–Binet, nor a minor determinant, nor an explicit re-triangularisation — the three
routes that had blocked this step earlier — because intrinsic-ness of `projNorm` makes the identity
a statement about *spans*, which the transposition does not move.

Updated state of the reduction-theory lane:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set as explicit inequalities                [PROVED]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [PROVED]
size reduction: |Uᵢⱼ| ≤ 1/2 after an integral shear    [PROVED]
uniqueness of the diagonal; the potential ∏ det Aₖ     [PROVED]
the Lovász bound from local minimality                 [PROVED]
greedy + size reduced ⟹ IsSiegel (4/3) 1              [PROVED]
the Siegel entry bound c dₖ γₖᵢ² ≤ K d'ᵢ              [PROVED]
projNorm is intrinsic (a squared distance)             [PROVED]
the swap identity and its strict decrease              [PROVED]
existence of a potential minimiser over the orbit      [next]
SL(n,ℤ)·𝔖 = X  (reduction)                            [OPEN]
the arithmetic step of Siegel finiteness               [OPEN]
```

The covering is now one existence statement away.  All the moves are in place — size reduction
leaves the potential fixed, a failed Lovász condition strictly lowers it, and the group elements
involved are integral shears and permutation matrices — so what remains is that the potential
`∏ₖ det Aₖ` attains its infimum over the `SL(n, ℤ)`-orbit, which is a discreteness statement about
the values of `det Aₖ` on sublattices.

## F28. The descent scheme and the reduction potential `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/PotentialDescent.lean`

- **`exists_terminal_of_contracting`** — if a potential is bounded below by a positive constant and
  every non-terminal state admits a successor whose potential is a fixed proportion `q < 1` of its
  own, then a terminal state exists.  Iterating the contraction drives the potential below the
  bound; the geometric limit supplies the index at which that happens.

This is the termination scheme of lattice basis reduction, and it replaces the "existence of a
minimiser" formulation recorded as next in F27.  That formulation is strictly harder: it needs the
infimum of the potential to be *attained*, whereas the descent only needs it to be *bounded below* —
and boundedness is what the geometry actually supplies.

`formal/GaloisForLFunctions/HTGeometry/SiegelPotential.lean`

- **`potentialOf`** — the product of the determinants of all leading minors of the form.
- **`potentialOf_form`** — its value in Jacobi coordinates: a product of powers of the diagonal,
  each `dₘ` appearing once per leading minor containing it.
- **`potentialOf_pos`**, `potentialOf_congr` — it is positive, and it depends on the form alone,
  never on a chosen decomposition.  This is what makes "contract the potential over the orbit"
  well-posed, and it rests on `det_leadingBlock_form` (F20).

Updated state of the reduction-theory lane:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set as explicit inequalities                [PROVED]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [PROVED]
size reduction: |Uᵢⱼ| ≤ 1/2 after an integral shear    [PROVED]
uniqueness of the diagonal; the potential ∏ det Aₖ     [PROVED]
the Lovász bound from local minimality                 [PROVED]
greedy + size reduced ⟹ IsSiegel (4/3) 1              [PROVED]
the Siegel entry bound c dₖ γₖᵢ² ≤ K d'ᵢ              [PROVED]
projNorm is intrinsic (a squared distance)             [PROVED]
the swap identity and its strict decrease              [PROVED]
the descent scheme; the potential is intrinsic         [PROVED]
the swap acts on the other leading minors              [next]
a positive lower bound for the potential               [next]
SL(n,ℤ)·𝔖 = X  (reduction)                            [OPEN]
the arithmetic step of Siegel finiteness               [OPEN]
```

The covering now decomposes into two named, finite tasks: (i) the swap leaves every leading minor
except the `(i+1)`-st unchanged — a permutation-invariance statement, since the spans of the other
prefixes are not moved; and (ii) `∏ₖ det Aₖ ≥ c > 0` on the orbit, which is Minkowski's convex body
theorem applied to each prefix sublattice (`exists_ne_zero_norm_le_of_covolume` is already in the
corpus).

## F29. A swap moves only one leading minor `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelSwapMinors.lean`

- **`permMatrix_congr_apply`** — conjugating by the permutation matrix of an involution rewrites the
  form entrywise: `A'ₐᵦ = A_{σa,σb}`.
- **`leadingBlock_swap_low`** — a leading block below both swapped indices is *equal* to the old
  one, since the transposition fixes every index it contains.
- **`det_leadingBlock_swap_high`** — a leading block above both swapped indices is the old one
  permuted by the restricted transposition, so its determinant is unchanged
  (`Matrix.det_submatrix_equiv_self`).

Together with `swap_d_eq_projNorm` (F27) this pins down the whole effect of a Lovász swap on the
potential: every factor `det Aₖ` with `k ≤ i` or `k ≥ i+2` is unchanged, and the single remaining
factor `det A_{i+1}` is multiplied by `d'ᵢ / dᵢ`, which `swap_d_lt` shows is `< 1` exactly when the
Lovász condition fails.

Updated state of the reduction-theory lane:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set as explicit inequalities                [PROVED]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [PROVED]
size reduction: |Uᵢⱼ| ≤ 1/2 after an integral shear    [PROVED]
uniqueness of the diagonal; the potential ∏ det Aₖ     [PROVED]
the Lovász bound from local minimality                 [PROVED]
greedy + size reduced ⟹ IsSiegel (4/3) 1              [PROVED]
the Siegel entry bound c dₖ γₖᵢ² ≤ K d'ᵢ              [PROVED]
projNorm is intrinsic (a squared distance)             [PROVED]
the swap identity and its strict decrease              [PROVED]
the descent scheme; the potential is intrinsic         [PROVED]
a swap moves only one leading minor                    [PROVED]
a positive lower bound for the potential               [next]
SL(n,ℤ)·𝔖 = X  (reduction)                            [OPEN]
the arithmetic step of Siegel finiteness               [OPEN]
```

Only one input to the covering is left: `∏ₖ det Aₖ ≥ c > 0` on the orbit.  Each `det Aₖ` is the
squared covolume of the sublattice spanned by the first `k` basis vectors, and Minkowski's convex
body theorem bounds it below by `Vₖ λ₁ᵏ / 2ᵏ`, where `λ₁` is the arithmetic minimum of the form —
fixed along the orbit, since congruate forms take the same values on the lattice.
