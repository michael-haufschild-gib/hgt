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

## F30. The lower bound for the potential `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelProjMono.lean`

- **`projNorm_mono`** — if one form dominates `λ` times another, so do their projected norms.  The
  proof is a two-sided use of the intrinsic characterisation (F26): the optimal competitor for the
  larger form is *a* competitor for the smaller one.
- `d_mono`, **`det_leadingBlock_mono`** — hence `λ^k · det Bₖ ≤ det Aₖ` for every leading minor.

`formal/GaloisForLFunctions/HTGeometry/SiegelIntegralMinor.lean`

- `det_leadingBlock_intCast`, `one_le_det_leadingBlock_of_int` — a form with integer entries has
  integral leading minors, and a positive integer is at least one.
- **`pow_le_det_leadingBlock`** — **if `A` dominates `λ` times an integral positive definite form,
  every leading minor of `A` is at least `λ^k`.**

This supplies the lower bound the descent scheme (F28) needs, and it does so **without geometry of
numbers**: the plan recorded in F29 was to apply Minkowski's convex body theorem to each prefix
sublattice, which would have required setting up a Haar measure and fundamental domain in each rank.
Integrality of the standard Gram matrix of integer vectors does the same work — its leading minors
are positive integers, hence at least one — and the uniform ellipticity bound
`A[v] ≥ λ‖v‖²` (already available as `quadForm_ge_of_sphere_bound`) transfers that to `A` through
`det_leadingBlock_mono`.  `exists_ne_zero_norm_le_of_covolume` is therefore not needed here.

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
a positive lower bound for the potential               [PROVED]
assembling the descent into SL(n,ℤ)·𝔖 = X             [next]
the arithmetic step of Siegel finiteness               [OPEN]
```

Every ingredient of the covering is now proved.  What is left is assembly: instantiate
`exists_terminal_of_contracting` with the orbit as the state space, `potentialOf` as the potential,
`IsSiegel (4/3) 1` as terminality, the lower bound above as `c`, and `3/4` as the contraction factor
— the step being size reduction followed by a swap at a failing index.

## F31. One descent step `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelDescentStep.lean`

- **`det_leadingBlock_succ`** — consecutive leading minors differ by exactly one diagonal entry,
  `det A_{k+1} = det A_k · dₖ`.
- **`isSiegel_two_of_terminal`** — with the Lovász threshold written as `3/4`, terminality of the
  descent *is* a Siegel bound: `(3/4) dᵢ ≤ projNorm i e_{i+1}` for all `i`, on a size reduced datum,
  gives `IsSiegel 2 1`.
- **`potentialOf_swap_lt`** — **a swap at a failing index contracts the potential by `3/4`.**  Only
  the minor separating the two swapped indices changes; it changes by the ratio of the new to the
  old Jacobi entry, which the failing condition bounds, and every other factor is positive and
  unaltered.

Writing the threshold as `3/4` rather than the sharp `4/3` in the Siegel parameter is what makes the
contraction factor uniform.  With the sharp threshold a failing swap gives only `d'ᵢ < dᵢ`, with no
fixed ratio, and the descent scheme (F28) would not apply; at the cost of `IsSiegel 2 1` in place of
`IsSiegel (4/3) 1` — immaterial, since a Siegel set for any parameter serves — every failing swap
now contracts by the constant `3/4`.

Updated state of the reduction-theory lane:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set as explicit inequalities                [PROVED]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [PROVED]
size reduction: |Uᵢⱼ| ≤ 1/2 after an integral shear    [PROVED]
uniqueness of the diagonal; the potential ∏ det Aₖ     [PROVED]
the Lovász bound from local minimality                 [PROVED]
the Siegel entry bound c dₖ γₖᵢ² ≤ K d'ᵢ              [PROVED]
projNorm is intrinsic (a squared distance)             [PROVED]
the swap identity and its strict decrease              [PROVED]
the descent scheme; the potential is intrinsic         [PROVED]
a swap moves only one leading minor                    [PROVED]
a positive lower bound for the potential               [PROVED]
terminality is a Siegel bound; a swap contracts by 3/4 [PROVED]
the orbit bookkeeping (integral unimodular closure)    [next]
SL(n,ℤ)·𝔖 = X  (reduction)                            [next]
the arithmetic step of Siegel finiteness               [OPEN]
```

Both hypotheses of `exists_terminal_of_contracting` are now discharged in the form the covering
needs: the potential is bounded below by `λ^k` (F30) and every non-terminal state contracts it by
`3/4` (above).  What is left is purely bookkeeping: a state type carrying "is a congruate of `A` by
an integral unimodular matrix", closed under the two moves — integral shears (F19) and permutation
matrices (F27) — so that the terminal state produced by the scheme is exhibited as lying in the
orbit.

## F32. The integral unimodular orbit `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelOrbit.lean`

- **`IsIntUnimodular`** — a real matrix that is the cast of an *invertible* integral matrix.  Phrased
  with `IsUnit g` in the matrix ring rather than `IsUnit g.det`, so that a move can be certified by
  exhibiting its inverse.
- `isIntUnimodular_one`, **`IsIntUnimodular.mul`** — closure.
- **`IsIntUnipotent.isIntUnimodular`** — a size-reducing shear qualifies: its integral form is upper
  triangular with unit diagonal, hence has determinant one.
- `permMatrixInt`, `permMatrix_eq_cast`, `permMatrixInt_mul_inv`,
  **`isIntUnimodular_permMatrix`** — a swap qualifies, certified by its explicit integral inverse
  `permMatrixInt σ⁻¹`.  (`Matrix.det_permutation` is not reachable under these imports; the explicit
  inverse avoids widening them.)
- **`InOrbit`**, `inOrbit_refl`, **`InOrbit.congr`** — the congruates of a form under this class,
  closed under further such congruence, hence under both reduction moves.

Updated state of the reduction-theory lane:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set as explicit inequalities                [PROVED]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [PROVED]
size reduction: |Uᵢⱼ| ≤ 1/2 after an integral shear    [PROVED]
uniqueness of the diagonal; the potential ∏ det Aₖ     [PROVED]
the Lovász bound from local minimality                 [PROVED]
the Siegel entry bound c dₖ γₖᵢ² ≤ K d'ᵢ              [PROVED]
projNorm is intrinsic (a squared distance)             [PROVED]
the swap identity and its strict decrease              [PROVED]
the descent scheme; the potential is intrinsic         [PROVED]
a swap moves only one leading minor                    [PROVED]
a positive lower bound for the potential               [PROVED]
terminality is a Siegel bound; a swap contracts by 3/4 [PROVED]
the orbit and its closure under both moves             [PROVED]
SL(n,ℤ)·𝔖 = X  (reduction)                            [next]
the arithmetic step of Siegel finiteness               [OPEN]
```

Every component of the covering is now proved.  What remains is a single assembly: take the state
type to be the Jacobi data whose form lies in `InOrbit A`, note that positive definiteness is
inherited along congruence so each state has Jacobi data, and feed
`exists_terminal_of_contracting` the potential `potentialOf`, the bound `λ^k` (F30), the factor
`3/4`, and the step "size-reduce, then swap at a failing index" (F19, F31), whose two moves are
unimodular by the above.

## F33. The two moves, inside the orbit `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelOrbitMoves.lean`

- **`JacobiData.posDef`** — the form of a Jacobi datum is positive definite (`Uᵀ D U` with `U`
  invertible and `D` positive diagonal).  This is what lets every congruate carry Jacobi data again,
  so the descent never leaves the world it started in.
- `potentialOf_shear_eq` — a shear leaves the potential fixed, because it leaves the diagonal fixed.
- **`exists_sizeReduced_inOrbit`** — size reduction, inside the orbit, at constant potential.
- **`exists_swap_inOrbit`** — a swap at a failing index, inside the orbit, contracting the potential
  by `3/4`.

Updated state of the reduction-theory lane:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set as explicit inequalities                [PROVED]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [PROVED]
size reduction: |Uᵢⱼ| ≤ 1/2 after an integral shear    [PROVED]
uniqueness of the diagonal; the potential ∏ det Aₖ     [PROVED]
the Lovász bound from local minimality                 [PROVED]
the Siegel entry bound c dₖ γₖᵢ² ≤ K d'ᵢ              [PROVED]
projNorm is intrinsic (a squared distance)             [PROVED]
the swap identity and its strict decrease              [PROVED]
the descent scheme; the potential is intrinsic         [PROVED]
a swap moves only one leading minor                    [PROVED]
a positive lower bound for the potential               [PROVED]
terminality is a Siegel bound; a swap contracts by 3/4 [PROVED]
the orbit and its closure under both moves             [PROVED]
both moves realised inside the orbit                   [PROVED]
the uniform lower bound along the orbit                [next]
SL(n,ℤ)·𝔖 = X  (reduction)                            [next]
the arithmetic step of Siegel finiteness               [OPEN]
```

Two steps remain for the covering, both bookkeeping.  First, the lower bound of F30 has to be taken
*along the orbit*: for a congruate `γᵀAγ` the comparison form is `γᵀγ`, which is integral because
`γ` is, and the ellipticity constant `λ` of `A` transfers unchanged since
`(γᵀAγ)[v] = A[γv] ≥ λ‖γv‖² = λ(γᵀγ)[v]`.  Second, the descent scheme is instantiated with a
constant terminal predicate — "some Siegel datum lies in the orbit" — so that failure of terminality
is available at *every* state, which is exactly what `exists_terminal_of_contracting` consumes.

## F34. The covering `SL(n,ℤ)·𝔖 = X` `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelCovering.lean`

- `dotProduct_self_le`, **`exists_ellipticity`** — a positive definite form dominates a multiple of
  the identity.  The sup norm of `Fin n → ℝ` is not the Euclidean one, so the constant picks up a
  factor `n`: `‖v‖²_∞ ≥ (v ⬝ᵥ v)/n`, and `λ = m/n` for the sphere bound `m` of
  `exists_lower_bound_of_isCompact`.
- `IsIntUnimodular.isUnit_det`, **`potentialOf_ge_of_inOrbit`** — the potential is bounded below
  along the orbit.  The comparison form of a congruate `γᵀAγ` is `γᵀγ`, integral because `γ` is, and
  the ellipticity constant transfers unchanged since `(γᵀAγ)[v] = A[γv] ≥ λ‖γv‖² = λ(γᵀγ)[v]`.
- **`exists_siegel_inOrbit`** — **every positive definite form is unimodularly equivalent to one
  satisfying the Siegel bounds `IsSiegel 2 1`.**

This is the covering half of Siegel's property, unconditional and closed.  The descent scheme is
instantiated with a *constant* terminal predicate — "some Siegel datum lies in the orbit" — so that
failure of terminality is available at every state, which is the shape the scheme consumes; the
alternative, a state-dependent predicate, fails because size reduction preserves the potential and
so cannot itself be a contraction.

Updated state of the reduction-theory lane:

```text
Jacobi coordinates                                     [PROVED]
the Siegel set as explicit inequalities                [PROVED]
quasi-diagonality: A[v] ≥ c ∑ dᵢ vᵢ² on 𝔖             [PROVED]
size reduction: |Uᵢⱼ| ≤ 1/2 after an integral shear    [PROVED]
uniqueness of the diagonal; the potential ∏ det Aₖ     [PROVED]
the Lovász bound from local minimality                 [PROVED]
the Siegel entry bound c dₖ γₖᵢ² ≤ K d'ᵢ              [PROVED]
projNorm is intrinsic (a squared distance)             [PROVED]
the swap identity and its strict decrease              [PROVED]
the descent scheme; the potential is intrinsic         [PROVED]
a swap moves only one leading minor                    [PROVED]
a positive lower bound for the potential               [PROVED]
terminality is a Siegel bound; a swap contracts by 3/4 [PROVED]
the orbit and its closure under both moves             [PROVED]
both moves realised inside the orbit                   [PROVED]
** SL(n,ℤ)·𝔖 = X  (the covering) **                   [PROVED]
the arithmetic step of Siegel finiteness               [OPEN]
```

One half of Siegel's property is therefore closed.  The other half — that a Siegel set meets only
finitely many of its own translates — still needs the arithmetic step recorded at F25: the analytic
input `c dₖ γₖᵢ² ≤ K d'ᵢ` is proved, integrality turns it into `dₖ ≤ K d'ᵢ` whenever `γₖᵢ ≠ 0`, and
what is missing is the passage from those support constraints to a bound on the entries themselves.

## F35. Arithmetic inputs to Siegel's finiteness `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelFinitenessInputs.lean`

- **`exists_nonzero_pair_of_mul_eq_one`** — if `M N = 1` then for each diagonal index some index
  pairs the two matrices nontrivially: otherwise the diagonal entry of the product would vanish.
- `one_le_sq_of_int_ne_zero` — a nonzero integer entry has square at least one.
- **`d_le_of_entry_ne_zero`** — hence `γₖᵢ ≠ 0` forces `c dₖ ≤ K d'ᵢ`: integrality collapses the
  analytic entry bound (F25) to a comparison of diagonal entries.
- **`exists_d_comparable`** — every index of the congruate has a partner at which the comparison
  holds in *both* directions, obtained by pairing `γ` against `γ⁻¹` on the diagonal.

### Where the finiteness argument still stands

The naive completions have been checked and do not close, which is worth recording so they are not
re-attempted:

* Pairing through the permutation supplied by `det γ ≠ 0` bounds only `d_{σ(i)} / d'ᵢ`, not
  `dₖ / d'ᵢ` for arbitrary `k` (noted at F25).
* Multiplying the two entry bounds gives `|γₖᵢ · (γ⁻¹)ᵢₖ| ≤ K` for *every* pair, but this bounds
  neither factor when the other vanishes.
* `exists_d_comparable` gives `d_{k(i)} ≍ d'ᵢ` at the paired index, and the Siegel bound
  `dₖ ≤ tⁿ d_l` for `k ≤ l` then bounds `γₖᵢ` for every `k ≥ k(i)` — but for `k < k(i)` the entry
  `dₖ` may be far smaller than `d_{k(i)}`, and the bound `γₖᵢ² ≤ K d'ᵢ / dₖ` is vacuous there.

So the missing step is exactly the control of the entries *above* the paired index, which in the
classical treatments comes from a Bruhat-type decomposition of `γ` rather than from the entry bound
alone.  Everything feeding it is proved.

Updated state of the reduction-theory lane:

```text
... (Jacobi coordinates through the covering)          [PROVED]
** SL(n,ℤ)·𝔖 = X  (the covering) **                   [PROVED]
the analytic entry bound c dₖ γₖᵢ² ≤ K d'ᵢ            [PROVED]
integrality: γₖᵢ ≠ 0 ⟹ c dₖ ≤ K d'ᵢ                   [PROVED]
the two-sided partner of each index                    [PROVED]
control of the entries above the paired index          [OPEN]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

## F36. The weighted isometry normal form `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelWeightedIsometry.lean`

- **`weightedIsometry_congr`** — stripping the unipotent factors from both sides of `A' = γᵀAγ`
  leaves `M = U γ (U')⁻¹` with `Mᵀ D M = D'`.
- **`weightedIsometry_entry_le`** — such an `M` satisfies `dₖ Mₖᵢ² ≤ d'ᵢ`, from
  `∑ₖ dₖ Mₖᵢ² = d'ᵢ`.

This is the right normal form for the finiteness half, and it corrects the shape of the remaining
problem.  Bounding `γ` is *equivalent* to bounding `M`, because the unipotent factors are bounded on
both sides — `U'` by size reduction (F19) and `U⁻¹` uniformly by compactness (F18).  A worked
example shows why this matters: for `A = diag(ε, 1/ε)` and `γ` the shear by `m`, the entry bound
alone gives only `m² ≤ K/ε²`, while size reduction of the *congruate* forces `m = 0`.  The entry
bound is therefore not the whole story, and any completion must use the unipotent data — which the
normal form isolates.

What remains is a statement purely about weighted isometries: an integral `γ = U⁻¹ M U'` with
`Mᵀ D M = D'`, both diagonals Siegel-ordered and both unipotent parts size reduced, has bounded
entries.  This is where the classical treatments invoke a Bruhat-type decomposition.

Updated state of the reduction-theory lane:

```text
... (Jacobi coordinates through the covering)          [PROVED]
** SL(n,ℤ)·𝔖 = X  (the covering) **                   [PROVED]
the analytic entry bound c dₖ γₖᵢ² ≤ K d'ᵢ            [PROVED]
integrality: γₖᵢ ≠ 0 ⟹ c dₖ ≤ K d'ᵢ                   [PROVED]
the two-sided partner of each index                    [PROVED]
the weighted isometry normal form γ = U⁻¹ M U'         [PROVED]
boundedness of a Siegel-ordered weighted isometry      [OPEN]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

## F37. Columns of a weighted isometry `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelIsometryColumns.lean`

- `transpose_mul_diagonal_apply` — the entries of `Mᵀ D`.
- **`weightedIsometry_col_sq`** — the congruence is an *identity* on columns:
  `∑ₖ dₖ Mₖᵢ² = d'ᵢ`.
- **`weightedIsometry_col_orth`** — distinct columns are `D`-orthogonal: `∑ₖ dₖ Mₖᵢ Mₖⱼ = 0`.
- **`weightedIsometry_support_sum_le`** — for an integral `M`, the weights of a column's support
  already sum to at most `d'ᵢ`.

This upgrades what F36 recorded.  Everything before used only the *inequality* `dₖ Mₖᵢ² ≤ d'ᵢ`, and
that inequality is provably too weak: in the two-dimensional example `d = d' = (ε, 1/ε)` it permits
an off-diagonal entry as large as `1/ε`, whereas the identity forces it to vanish — because the
diagonal entry is a nonzero integer, so its own term already exhausts `d'ᵢ`, leaving nothing for the
other.  The support bound is the general form of that argument.

Updated state of the reduction-theory lane:

```text
... (Jacobi coordinates through the covering)          [PROVED]
** SL(n,ℤ)·𝔖 = X  (the covering) **                   [PROVED]
the analytic entry bound c dₖ γₖᵢ² ≤ K d'ᵢ            [PROVED]
integrality: γₖᵢ ≠ 0 ⟹ c dₖ ≤ K d'ᵢ                   [PROVED]
the weighted isometry normal form γ = U⁻¹ M U'         [PROVED]
the column identity, orthogonality and support bound   [PROVED]
boundedness of a Siegel-ordered weighted isometry      [OPEN]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

## F38. The exact column sum `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelColumnSum.lean`

- **`siegel_col_sum_eq`** — the diagonal entry of a congruate is an *exact* weighted sum:
  `∑ₖ dₖ ((U γ)ₖᵢ)² = A'ᵢᵢ`.
- **`siegel_col_sum_bound`** — hence `∑ₖ dₖ ((U γ)ₖᵢ)² ≤ (1 + n tⁿ/4) d'ᵢ`.

This is the correct strengthening of the entry bound (F25), which records only the single-term
consequence `dₖ γₖᵢ² ≤ K d'ᵢ`.

It also corrects a mismatch that F37 left implicit.  The support argument proved there applies to an
*integral* weighted isometry, but the isometry `M = U γ (U')⁻¹` of F36 is not integral — only `γ` is.
The exact sum above resolves which object carries which property: the weights `dₖ` attach to the
columns of `U γ`, while integrality attaches to `γ`.  The two are related by the bounded factors `U`
and `U⁻¹`, and any completion of the finiteness half has to pass through that relation rather than
apply the support bound to `γ` directly.

Updated state of the reduction-theory lane:

```text
... (Jacobi coordinates through the covering)          [PROVED]
** SL(n,ℤ)·𝔖 = X  (the covering) **                   [PROVED]
the analytic entry bound c dₖ γₖᵢ² ≤ K d'ᵢ            [PROVED]
integrality: γₖᵢ ≠ 0 ⟹ c dₖ ≤ K d'ᵢ                   [PROVED]
the weighted isometry normal form γ = U⁻¹ M U'         [PROVED]
the column identity, orthogonality and support bound   [PROVED]
the exact column sum ∑ₖ dₖ ((Uγ)ₖᵢ)² ≤ K d'ᵢ         [PROVED]
reconciling integrality of γ with the weights of Uγ    [OPEN]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

## F39. The support weight of a column `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelSupportWeight.lean`

- **`siegel_col_weight_sum`** — `c ∑ₖ dₖ γₖᵢ² ≤ (1 + n tⁿ/4) d'ᵢ`: the weighted column bound holds
  for `γ` itself, not only for `U γ`.
- **`siegel_support_weight_sum`** — hence, for integral `γ`, the weights of the *support* of a column
  sum to at most a multiple of `d'ᵢ`.

This closes the reconciliation left open at F38.  The obstruction there was that the weights attach
to the columns of `U γ` while integrality attaches to `γ`; quasi-diagonality (F18) is exactly the
bridge, since it bounds `∑ₖ dₖ vₖ²` by `A[v]` for *every* `v` — in particular for the columns of `γ`.
No new geometry was needed: the missing step was an application of a lemma proved much earlier in
the lane, and the earlier single-term entry bound (F25) was simply a weaker consequence of the same
inequality.

Updated state of the reduction-theory lane:

```text
... (Jacobi coordinates through the covering)          [PROVED]
** SL(n,ℤ)·𝔖 = X  (the covering) **                   [PROVED]
the analytic entry bound c dₖ γₖᵢ² ≤ K d'ᵢ            [PROVED]
the weighted isometry normal form γ = U⁻¹ M U'         [PROVED]
the column identity, orthogonality and support bound   [PROVED]
the exact column sum ∑ₖ dₖ ((Uγ)ₖᵢ)² ≤ K d'ᵢ         [PROVED]
the support weight bound for γ itself                  [PROVED]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

The finiteness half now has, for every column `i` of every `γ` carrying one Siegel form to another:
`∑_{k : γₖᵢ ≠ 0} dₖ ≤ (K/c) d'ᵢ`, together with the same statement for `γ⁻¹` with the roles of `d`
and `d'` exchanged, and the two-sided partner of F35.  What is still missing is the combinatorial
step that turns these support constraints into a bound on the entries themselves.

## F40. The top diagonal entries are comparable `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelTopEntry.lean`

- **`exists_row_nonzero`** — every row of an invertible matrix has a nonzero entry (from the
  pairing of F35 applied to `γ γ⁻¹ = 1`).
- **`d_top_le`** — **`c d_l ≤ K tⁿ d'_l` for the largest index `l`**, with no hypothesis on where in
  the row the nonzero entry sits: whichever column `i` it occupies satisfies `i ≤ l`, so the Siegel
  ordering absorbs it.

The *row* direction is what makes this work, and the asymmetry is worth recording.  Running the same
argument down a column gives nothing: a nonzero `γ_{k i}` yields `c dₖ ≤ K d'ᵢ`, and for `k < l` the
Siegel ordering then runs the wrong way — `d_l` is not bounded by `dₖ`.  So the argument closes at
the top index and nowhere else, which is precisely why the finiteness half needs more than the entry
bound, and why the descending induction of the classical proof starts where it does.

Updated state of the reduction-theory lane:

```text
... (Jacobi coordinates through the covering)          [PROVED]
** SL(n,ℤ)·𝔖 = X  (the covering) **                   [PROVED]
the weighted isometry normal form γ = U⁻¹ M U'         [PROVED]
the column identity, orthogonality and support bound   [PROVED]
the support weight bound for γ itself                  [PROVED]
the top diagonal entries are comparable                [PROVED]
the descending induction to the lower indices          [OPEN]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

## F41. The top row is bounded `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelTopRow.lean`

- **`row_top_bounded`** — **`c² γₗᵢ² ≤ K² t²ⁿ` for every `i`**, where `l` is the largest index.

This is the first point in the finiteness half where an actual *entry* of the conjugating matrix is
bounded, rather than merely constrained.  The chain is
`dₗ γₗᵢ² ≲ d'ᵢ ≲ d'ₗ ≲ dₗ`, and `dₗ` cancels — the last link being the reverse of `d_top_le` (F40),
which is that same lemma applied to `γ⁻¹`.

It is the base case of the descending induction of Siegel's finiteness.  The induction step must
pass to the complement of the top coordinate, where the argument repeats with `n` replaced by
`n − 1`; that requires a sub-structure on the Jacobi data, which is the next brick.

Updated state of the reduction-theory lane:

```text
... (Jacobi coordinates through the covering)          [PROVED]
** SL(n,ℤ)·𝔖 = X  (the covering) **                   [PROVED]
the weighted isometry normal form γ = U⁻¹ M U'         [PROVED]
the column identity, orthogonality and support bound   [PROVED]
the support weight bound for γ itself                  [PROVED]
the top diagonal entries are comparable                [PROVED]
the top row of γ is bounded                            [PROVED]
the induction step to n − 1                            [OPEN]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

## F42. Truncating Jacobi data `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelTruncation.lean`

- **`JacobiData.trunc`** — the leading `k × k` part of a Jacobi datum is again a Jacobi datum.
- **`JacobiData.trunc_form`** — its form is the leading block of the original form (this is
  `leadingBlock_congr`, F20, read in the other direction).
- **`trunc_isSiegel`**, **`trunc_sizeReduced`** — both Siegel bounds and size reduction are
  inherited: the diagonal bound constrains consecutive indices, all of which survive truncation, and
  the other two are entrywise.

This is the structure the descending induction runs on.  Having bounded the top row (F41), the
argument restricts to the leading block and repeats with `n` replaced by `n − 1`; what the induction
still needs is that the *conjugation* descends — that the leading block of `γᵀAγ` differs from the
congruate of the leading blocks by contributions from the top row, which F41 has bounded.

Updated state of the reduction-theory lane:

```text
... (Jacobi coordinates through the covering)          [PROVED]
** SL(n,ℤ)·𝔖 = X  (the covering) **                   [PROVED]
the weighted isometry normal form γ = U⁻¹ M U'         [PROVED]
the column identity, orthogonality and support bound   [PROVED]
the support weight bound for γ itself                  [PROVED]
the top diagonal entries are comparable                [PROVED]
the top row of γ is bounded                            [PROVED]
truncation of Jacobi data, with inherited bounds       [PROVED]
descent of the conjugation to the leading block        [OPEN]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

## F43. Comparable minors give comparable diagonals `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelMinorComparison.lean`

- **`d_le_of_det_le`** — if the leading minors of two Jacobi data are comparable within a factor `C`
  in both directions, then their diagonals are comparable within `C²`.  Each `dₗ` is the ratio of
  consecutive minors (F31), so the comparison transfers with the constant squared.

This reshapes what the finiteness half is waiting for.  The descending induction of F41–F42 is one
route; this is another, and a shorter one: with `dₖ ≍ d'ₖ` for *all* `k`, the entry bound
`γₖᵢ² ≤ (K/c) d'ᵢ / dₖ` becomes `≍ dᵢ / dₖ`, which the Siegel ordering bounds outright whenever
`i ≤ k`, while the entries with `i > k` are exactly the ones size reduction of `U'` controls — the
mechanism already isolated by the worked example at F36.

The remaining input is then a single statement about minors rather than an induction over indices:
**the leading minors of two reduced bases of one lattice are comparable.**  This holds because
reduction makes each leading minor comparable to the minimum covolume over sublattices of that rank,
which is a lattice invariant; it is a Minkowski-type input, and it is the one place in the finiteness
half where geometry of numbers genuinely enters.

Updated state of the reduction-theory lane:

```text
... (Jacobi coordinates through the covering)          [PROVED]
** SL(n,ℤ)·𝔖 = X  (the covering) **                   [PROVED]
the weighted isometry normal form γ = U⁻¹ M U'         [PROVED]
the column identity, orthogonality and support bound   [PROVED]
the support weight bound for γ itself                  [PROVED]
the top diagonal entries are comparable                [PROVED]
the top row of γ is bounded                            [PROVED]
truncation of Jacobi data, with inherited bounds       [PROVED]
comparable minors ⟹ comparable diagonals              [PROVED]
the leading minors of two reduced bases are comparable [OPEN]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel)                      [OPEN]
```

## F44. The leading minors of a reduced form are minimal in its orbit `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelSubsetProduct.lean`,
`SiegelWeightedGram.lean`, `SiegelGramDomination.lean`, `SiegelMinorLowerBound.lean`

The open item of F43 is closed.  The route turned out not to need Minkowski's convex body theorem,
nor Hermite normal form, nor any echelon reduction of the sublattice basis — three approaches that
were tried and abandoned in that order.  What it needs is Cauchy–Binet, which the corpus already
owned (`GaloisForLFunctions.det_mul_eq_sum_fun`, `factorial_mul_det_mul` in `HTGeometry/CauchyBinet`).

The `k`-th leading minor of `A' = γᵀAγ` is the Gram determinant of the frame `C` of the first `k`
columns of `γ`, taken in the form `A`:

  `leadingBlock_congr_frame` : `leadingBlock hk (γᵀ A γ) = Cᵀ A C`.

Three steps then bound it from below by the `k`-th leading minor of `A`.

- **Domination** (`det_congr_ge`).  Quasi-diagonality `c · Σ dₘ vₘ² ≤ A[v]` on a Siegel set
  (`exists_quasiDiagonal`, F13) upgrades from vectors to determinants without any Loewner-order
  determinant monotonicity: every Jacobi diagonal entry of `CᵀAC` is *attained* at an explicit
  vector (`projNorm_eq_form_sub`, F26), and that same vector bounds the corresponding entry for
  `Cᵀ D C` from above (`projNorm_le_form_sub`).  Multiplying the `k` comparisons gives
  `cᵏ · det(Cᵀ D C) ≤ det(Cᵀ A C)`.
- **Cauchy–Binet** (`factorial_mul_det_weightedGram`).  For a diagonal weight,
  `k! · det(Cᵀ D C) = Σ_f (∏_b d_{f b}) · det(C∘f)²`, the sum over *all* index functions.  All terms
  are nonnegative; the non-injective `f` contribute zero.  Since the frame is integral, some maximal
  minor is a nonzero integer (found by positivity of the determinant, not by a rank argument), so its
  square is at least one.
- **The weight comparison** (`prod_castLE_le_prod_of_injective`).  For an injective `f`, the selected
  indices listed in increasing order satisfy `sⱼ ≥ j`, so the Siegel growth bound `dᵢ ≤ tⁿ dⱼ`
  (`d_le_pow_n`) compares the selected weight product with the leading one factor by factor.  The
  increasing enumeration is `Finset.orderIsoOfFin` on the image; `le_val_of_strictMono` supplies
  `sⱼ ≥ j`.

Together:

  **`exists_minor_lower_bound`** — for every `t ≥ 1, u` there is `C > 0` such that whenever `J` is
  Siegel-`(t,u)` and `J'.form = γᵀ J.form γ` with `γ` integral unimodular,
  `det Aₖ ≤ C · det A'ₖ` for every `k ≤ n`.

Applying it in both directions — the reverse needs `IsIntUnimodular.exists_inv`, the integral inverse
— and feeding F43:

  **`exists_d_comparable_of_siegel`** — two Siegel-reduced forms in one integral orbit have
  `dₗ ≤ C² d'ₗ` for every `l`, with `C` depending only on `n, t, u`.

Note that this half of the argument uses no size reduction: `exists_quasiDiagonal` and the weight
comparison are consequences of the two Siegel bounds alone.

## F45. Siegel's finiteness property `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/SiegelEntryBoundSiegel.lean`,
`SiegelIsometryVanishing.lean`, `SiegelFiniteness.lean`

With `d ≍ d'` in hand the finiteness half closes, and it closes by a mechanism different from the
descending induction of F41–F42, which is now superseded.

- **The entry bound without size reduction** (`form_diag_le_siegel`, `siegel_entry_bound_of_siegel`,
  `d_le_of_entry_ne_zero_of_siegel`).  `A_jj = Σ_m d_m U_{mj}²` runs only over `m ≤ j`, where
  `|U_{mj}| ≤ u` and `d_m ≤ tⁿ d_j`; so `A_jj ≤ n u² tⁿ d_j` with no `|U| ≤ 1/2` hypothesis.  The
  whole finiteness argument is therefore a statement about the Siegel set as defined, not about a
  size-reduced subset of it.
- **The threshold** .  A nonzero entry of `δ = γ⁻¹` forces `d_a ≤ R d_b` with
  `R = C² · n u² tⁿ / c`; this is `d_le_of_entry_ne_zero_of_siegel` applied to `δ`, combined with
  F44.
- **The vanishing** (`triangular_conjugate_entry_zero`).  Write the inverse isometry as
  `M⁻¹ = U' δ U⁻¹`.  Both triangular factors move indices in the direction that *improves* the weight
  comparison — `U'` upper triangular forces `a ≥ i`, and `U⁻¹` upper triangular (`inv_upper`) forces
  `b ≤ k` — so every surviving term needs `δ_{ab} ≠ 0` with `d_i ≤ tⁿ d_a ≤ tⁿ R d_b ≤ t²ⁿ R d_k`.
  Beyond that threshold the entry is zero.
- **The isometry is bounded** (`isometryInv`, `isometryInv_mul`, `isometryInv_eq`).  From
  `MᵀDM = D'` the weighted transpose `(M⁻¹)_{ik} = d_k M_{ki} / d'_i` is a left inverse, hence *the*
  inverse.  So the vanishing above transfers to `M` itself: `M_{ki} = 0` once `d_i > t²ⁿ R d_k`, and
  where it does not vanish `d_k M_{ki}² ≤ d'_i ≤ C² d_i ≤ C² t²ⁿ R d_k` bounds it.  This is the step
  the earlier attempts kept missing: `M` is *not* bounded by the isometry relation alone — the
  relation only says `‖D^{1/2} M D'^{-1/2}‖ = 1` — and it is not bounded by integrality alone either,
  since `M` is not integral.  It is bounded because integrality of `γ⁻¹` kills the entries the
  isometry relation cannot control.
- **The conclusion** (`exists_gamma_bound`, `siegel_finiteness`).  `γ = U⁻¹ M U'` with all three
  factors bounded, so `|γ_{ki}| ≤ n²·C_u·B·u`; and bounded integral matrices form a finite set.

  **`siegel_finiteness`** — `{γ integral unimodular : ∃ J, J' Siegel-(t,u) with J'.form = γᵀ J.form γ}`
  is finite.

Updated state of the reduction-theory lane:

```text
... (Jacobi coordinates through the covering)          [PROVED]
** SL(n,ℤ)·𝔖 = X  (the covering) **                   [PROVED]
comparable minors ⟹ comparable diagonals              [PROVED]
the leading minors of two reduced bases are comparable [PROVED]
d ≍ d' for two reduced forms in one orbit              [PROVED]
the weighted isometry is bounded                       [PROVED]
** {γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel finiteness) **     [PROVED]
```

Both halves of the Siegel property are now unconditional in Lean.  What stands between them and
`isFinitelyPresented_specialLinearGroup_of_siegel` (F7) is only that its hypotheses are stated for an
**open connected** `V ⊆ posDefCone n` whose translates cover, whereas the Siegel set is closed.  The
bridge is:

```text
Jacobi coordinates are continuous functions of the form      [OPEN]
the open Siegel set (strict inequalities) is open            [OPEN]
it is connected (continuous image of a convex parameter set) [OPEN]
its translates cover (the closed set of F32 sits inside it)  [OPEN]
meetSet V is finite (F45)                                    [PROVED]
SL(n,ℤ) is finitely presented                                [OPEN]
```

Continuity of the Jacobi coordinates is elementary and does not need invariance of domain: the
diagonal is a ratio of leading minors, `d_i = det A_{i+1} / det A_i` (F31), and the unipotent factor
satisfies the LDL recursion `d_i U_{ij} = A_{ij} − Σ_{m<i} d_m U_{mi} U_{mj}`, which is a strong
induction on `i`.

**Scope note.**  `SL(n,ℤ)` finitely presented gives `K₂(ℤ)` finitely generated, hence — with Moore —
`K₂(ℚ)` torsion.  That does *not* advance the Deninger card, because `milnorKDeg_numberField_torsion`
already gives `K_m^M(ℚ)` torsion for every `m ≥ 2` unconditionally (Bass–Tate, degree drop
`m ≥ [F:ℚ]+1`).  The card needs `K₂(𝒪_F)` for `[F:ℚ] = d ≥ 2`, so the reduction theory has to be run
for `SL_n(𝒪_F)` acting on the `F`-Hermitian sub-cone of `posDefCone(nd)` — a linear slice of the same
cone, so Macbeath's convex-domain criterion still applies verbatim, and the finiteness half is
inherited from the ambient group.  It is the *covering* half that has to be redone over `𝒪_F`
(Humbert reduction).  That is the next layer of this lane.

## F46. `SL(n, ℤ)` is finitely presented `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/JacobiUniqueness.lean`, `JacobiContinuity.lean`,
`JacobiSignFlip.lean`, `OpenSiegelSet.lean`

Macbeath's criterion (F7) wants an **open connected** fundamental set; the Siegel set is closed.  The
bridge is that the Jacobi coordinates are continuous functions of the form, so replacing `≤` by `<`
gives an open set that still contains the closed Siegel set of the covering theorem.

- **Uniqueness and the recursion** (`form_apply`, `ldl_recursion`, `U_unique`).  Reading `A = UᵀDU`
  at `(i,j)` and separating the diagonal term gives `dᵢ Uᵢⱼ = Aᵢⱼ − Σ_{m<i} dₘ Uₘᵢ Uₘⱼ`, since
  `Uₘᵢ = 0` for `m > i` and `Uᵢᵢ = 1`.  With `d` already determined by the minors (F31), a strong
  induction on the row index determines `U`.  So the Jacobi datum of a form is unique, and the
  recursion is exactly what makes it continuous.
- **Continuity** (`jacOf`, `continuous_jacOf_d`, `continuous_jacOf_U`).  `dᵢ = det A_{i+1} / det A_i`
  with positive denominator; then the recursion, by the same strong induction.  No invariance of
  domain, no inverse function theorem.
- **Sign normalisation** (`JacobiData.flip`, `exists_siegel_inOrbit_det_one`).  The covering theorem
  produces an integral matrix of determinant `±1`, but `SL(n,ℤ)` wants `+1`.  Conjugating a Jacobi
  datum by a diagonal sign matrix `s` sends `U` to `sᵢ Uᵢⱼ sⱼ` and fixes `d`, so it preserves both
  Siegel bounds; multiplying the reducing matrix by that sign matrix corrects the determinant.
- **The open Siegel set** (`openSiegelSet n t u`, strict bounds).  Open, by continuity.  Nonempty for
  `t, u > 1`, the identity form being inside.  Connected, because
  `coneMat '' openSiegelSet = psiParam '' siegelParam` — the parameter region `siegelParam` is cut out
  by linear equalities and strict linear inequalities, hence convex, hence preconnected, and
  `Subtype.val` is inducing.  Its translates cover with `(t,u) = (3,2)`, since `IsSiegel 2 1` implies
  the strict bounds.  Its overlap set is finite by F45, the map `g ↦ (slReal g)ᵀ` being injective.

  **`isFinitelyPresented_specialLinearGroup`** — `SL(n, ℤ)` is finitely presented, for every `n`.

Final state of the reduction-theory lane over `ℤ`:

```text
Jacobi coordinates, uniqueness, continuity              [PROVED]
SL(n,ℤ)·𝔖 = X  (the covering), with det = 1            [PROVED]
{γ : γ𝔖 ∩ 𝔖 ≠ ∅} finite (Siegel finiteness)            [PROVED]
the open Siegel set: open, nonempty, connected          [PROVED]
** SL(n, ℤ) is finitely presented **                    [PROVED]
```

### What this does and does not give

It gives the geometric input of the `K₂` finite-generation chain **over `ℤ`**.  Closing that chain
still needs, at finite level `n`:

```text
E_n(ℤ) = SL_n(ℤ)  (transvections generate over a Euclidean domain)   [OPEN]
K₂(n, ℤ) central in St_n(ℤ)  (the corpus owns only the stable form,
  `KTwo_mem_center_of_card`, which needs a spare index)              [OPEN]
K₂(ℤ) = K₂(n, ℤ) for large n  (stability)                           [OPEN]
```

and it does **not** advance the Deninger card, for the reason recorded at F45: `K_m^M(ℚ)` is already
torsion for every `m ≥ 2` by Bass–Tate.  The card needs `[F:ℚ] ≥ 2`, hence Humbert reduction for
`𝒪_F`-lattices.

### What the `𝒪_F` layer inherits and what it does not

Writing `N = n·[F:ℚ]` and `Y = {A ∈ posDefCone N : A is 𝒪_F-Hermitian}`, the group `SL_n(𝒪_F)` acts on
`Y`, which is the intersection of the open convex cone with a linear subspace — so it is again open
and convex, and Macbeath's convex-domain criterion applies verbatim.  Moreover the **finiteness**
half is inherited for free: if `V ⊆ Y` is contained in an ambient open Siegel set, then
`{γ ∈ SL_n(𝒪_F) : γV ∩ V ≠ ∅} ⊆ {λ ∈ SL_N(ℤ) : λV ∩ V ≠ ∅}`, which F45 makes finite.

What does not transfer is the **covering**: ambient reduction of `A ∈ Y` produces `λ ∈ SL_N(ℤ)` with
`λ·A` reduced, but `λ` need not be `𝒪_F`-linear and `λ·A` need not lie in `Y`.  So the covering has to
be redone with `𝒪_F`-linear moves.  The two places where the ℤ-argument uses more than `𝒪_F` offers:

- *size reduction* uses division with remainder.  Over `𝒪_F` the replacement is the covering radius:
  `𝒪_F` is a full lattice in `F ⊗ ℝ`, so there is `C` with `∀ x, ∃ a ∈ 𝒪_F, ‖x − a‖ ≤ C`.  The
  descent only ever used *boundedness* of the shear, never `≤ 1/2`, so this is a constant change.
- *the swap* replaces a basis vector by another vector of a basis.  Over `𝒪_F` a primitive vector
  need not extend to a basis; the replacement is Bass's stable range theorem, `SL_n(𝒪)` transitive on
  unimodular rows for `n ≥ 3`.

The Jacobi diagonal also becomes a tuple indexed by the archimedean places, so the potential and the
Lovász condition become multi-dimensional.  That is the next layer of this lane.

## F47. Design of the `𝒪_F` layer

Two formulations of the symmetric space of `SL_n(𝒪_F)` were compared before starting.

**(a) Place-indexed.**  `∏_{v real} P_n(ℝ) × ∏_{v complex} P_n(ℂ)`, an open convex subset of a real
vector space, so Macbeath applies verbatim.  Rejected as the primary formulation: the finiteness half
(F45) would have to be redone from scratch, and it is the harder half.

**(b) Inside the ambient cone.**  `N = n·[F:ℚ]`, `SL_n(𝒪_F) ↪ SL_N(ℤ)` (the determinant of the
ℤ-linear map is `N_{F/ℚ}(det) = 1`), and `Y ⊆ posDefCone N` the sub-symmetric space.  `Y` is the
intersection of the open convex cone with a linear subspace, hence open and convex in that subspace,
so Macbeath still applies; and — the decisive point — the **finiteness half is inherited free**:

  `{γ ∈ SL_n(𝒪_F) : γV ∩ V ≠ ∅} ⊆ {λ ∈ SL_N(ℤ) : λV ∩ V ≠ ∅}`,

which F45 makes finite as soon as `V` lies inside an ambient Siegel set.  Formulation (b) is the one
to build.

### The description of `Y`

For `α ∈ 𝒪_F` let `M_α` be its matrix on `𝒪_F^n ≅ ℤ^N`.  A real symmetric `A` is the trace form of an
`F_ℝ`-Hermitian form iff `A(αx, y) = A(x, ᾱy)`, and `ᾱ ∈ F_ℝ` is not in `F` when `F` has a complex
place — so the defining equations of `Y` are linear with irrational coefficients in general, and the
clean intrinsic description is instead

  `Y = {A : A is invariant under the compact torus ∏_{v complex} U(1)}`.

**For `F` totally real this collapses**: there is no torus, `ᾱ = α`, and

  `Y = {A ∈ posDefCone N : ∀ α ∈ 𝒪_F, M_αᵀ A = A M_α}`,

a linear subspace cut out by *integral* equations, needing no archimedean machinery in the statement.
Note also that the `A(αx,y) = A(x,αy)` condition is **incompatible with positive definiteness** when
`F` has a complex place — `H_v(ix,ix) = −H_v(x,x)` — which is exactly why the involution cannot be
dropped there.  So the first milestone is `F` totally real, and it is not merely a special case: it is
the case where the formulation is intrinsic.

### What the ℤ-machinery already gives on `Y`

The Jacobi decomposition of `A ∈ Y` is the ordinary real one — no complex LDL is needed.  A complex
Hermitian `H = UᴴDU` has real form `Ũᵀ D̃ Ũ` in the basis `(e₁, ie₁, e₂, ie₂, …)`, with `Ũ` again
unipotent upper triangular (its diagonal blocks are `I₂`) and `D̃ = diag(d₁,d₁,d₂,d₂,…)`; by
`U_unique`/`d_unique` (F46) that *is* the real Jacobi datum.  So the `𝒪_F`-structure appears purely as
a constraint on the ambient Jacobi data, and every continuity, uniqueness, minor and isometry lemma of
F31–F46 applies unchanged.

### What has to be built

```text
𝒪_F as a ℤ-algebra acting on ℤ^N; the subspace Y; Y open convex in it     [OPEN]
size reduction over 𝒪_F: the covering radius                             [mathlib]
  `ZSpan.floor`, `ZSpan.fract_apply`, `ZSpan.norm_fract_le` give
  `∀ x, ∃ v ∈ span_ℤ b, ‖x − v‖ ≤ Σ ‖b i‖` in five lines; for 𝒪_F use
  `NumberField.mixedEmbedding.latticeBasis`.
integrality over 𝒪_F: `1 ≤ ∏_v v(α)^{mult v} = |N_{F/ℚ}(α)|` for α ≠ 0    [mathlib]
  `NumberField.InfinitePlace.prod_eq_abs_norm` plus `N(α) ∈ ℤ`.
the 𝒪_F-swap: a primitive vector extends to a basis                       [OPEN]
  over ℤ this was automatic; over 𝒪_F it is Bass's stable range theorem,
  `SL_n(𝒪)` transitive on unimodular rows for n ≥ 3.
the Humbert descent: potential = ∏_i covol(𝒪_F-span of b₁..b_i)²          [OPEN]
  bounded below by discreteness of the lattice of sublattice covolumes.
Humbert-reduced ⟹ contained in an ambient ℤ-Siegel set                    [OPEN]
  this is what buys the finiteness half from F45.
SL_n(𝒪_F) finitely presented                                              [OPEN]
```

### The parallel algebraic lane

`SL_n(𝒪_F)` finitely presented is the *geometric* input of the `K₂` chain.  The algebraic inputs, all
still open and independent of the above, are: `E_n(𝒪_F) = SL_n(𝒪_F)` for `n ≥ 3`;
`K₂(n,𝒪_F)` central in `St_n(𝒪_F)` — the corpus owns only the stable form `KTwo_mem_center_of_card`,
which needs a spare index and so applies to `St(R, ℕ)`, where the group is central but not finitely
generated; and van der Kallen stability `K₂(n,R) ≅ K₂(R)`.  A partial result available *now* from
`isFinitelyPresented_specialLinearGroup`: with `G_n := image(St_n(ℤ) → St_{n+1}(ℤ)) =
closure(indexGens (Fin n))`, every element of `G_n ∩ KTwo ℤ (Fin (n+1))` has a spare index, hence is
central, so `ker(G_n → E_n(ℤ))` is finitely generated by `fg_ker_of_central_of_isFinitelyPresented`
once `E_n(ℤ) = SL_n(ℤ)` is available.  That gives finite generation of the *image* of `K₂(n,ℤ)` at
level `n+1`; passing to `K₂(ℤ)` is exactly where stability is needed.

## F48. The `𝒪_F` layer: foundations `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/OrderBlockEmbedding.lean`, `BalancedOrderForm.lean`,
`OrderSymmetricSpace.lean`, `OrderSiegelFiniteness.lean`, `BlockJacobiData.lean`

Everything here is for an arbitrary commutative ring `R` free of finite rank `d` over `ℤ` — no number
field machinery.  Where the construction would be vacuous (an order with a complex place admits no
positive definite balanced form) the statements are true and empty, so nothing is lost by the
generality.

- **`blockEmbed`** flattens an `n × n` matrix of `d × d` blocks to an `nd × nd` matrix, with the
  block-major index bijection `finProdFinEquiv (i,k) = k + d·i`, so blocks are *contiguous* and the
  ambient order restricts to the lexicographic order on `(block, position)`.  It is unital,
  multiplicative and injective.  Composing with `Algebra.leftMulMatrix ω` gives **`orderRep`**, and
  `isIntUnimodular_orderRep` puts units of `M_n(R)` into `IsIntUnimodular` — the interface of F45.
- **`balancedSubspace`** is the forms for which multiplication by every ring element is self-adjoint.
  `balancedSubspace_congr` : congruence by `orderRep` preserves it, because scalars are central in
  `M_n(R)` and `orderRep` is multiplicative.
- **`orderForms = symmMatrices (nd) ⊓ balancedSubspace`**, **`orderCone`** its positive definite
  locus — open (preimage of `posDefCone` under the inclusion) and convex (linear preimage).
  `SL_n(R)` acts by `A ↦ ρ(M⁻¹)ᵀ A ρ(M⁻¹)`; the inverse is what makes it a *left* action while
  keeping the congruence in the `γᵀAγ` shape that preserves balancedness.
  **`isFinitelyPresented_of_orderSiegel`** is Macbeath's criterion in this setting: a connected open
  `V` whose translates cover and whose overlaps are finite presents `SL_n(R)`.
- **`orderMeet_finite`** is the claim of F47 made good: if every `A ∈ V` is Siegel-reduced *for the
  ambient integral group*, the overlap set of `V` under `SL_n(R)` is finite.  The proof is three
  lines on top of F45 — the conjugators are `IsIntUnimodular`, they carry one ambient Siegel-reduced
  form to another, and `M ↦ orderInvRep ω M` is injective.  **The finiteness half over an order is
  therefore closed.**
- **`blockJacobi`, `JacobiData.twist`, `blockJacobi_twist_form`** compute the ambient Jacobi data of
  `Wᵀ E W` with `E` block diagonal and `W` unipotent upper triangular: the diagonal is the
  concatenation of the blocks' diagonals and the unipotent factor is `blockEmbed(diag Uₘ) · W`.

### The remaining input, stated exactly

What is left is the covering, and the analysis of what it needs is now precise.  Let `H` be the
`R ⊗ ℝ`-bilinear form with `A = Tr(H)`, and let `H = μᵀ Δ μ` be its Gram–Schmidt over `R ⊗ ℝ`
(available because `R ⊗ ℝ` is a product of fields and the leading minors of `H` are positive at every
place).  Then

  `A = Wᵀ E W`,  `W = blockEmbed(regRep_ℝ μ)`,  `E = blockEmbed(diag Eₘ)`,
  `Eₘ(k,l) = Tr(Δₘ ω_k ω_l) = (Ωᵀ diag(Δ_{m,v}) Ω)(k,l)`,   `Ω_{v,k} = σ_v(ω_k)`,

and `blockJacobi_twist_form` turns that into the ambient Jacobi data outright: ambient `d` at
`(m,k)` is the `k`-th LDL entry of `Eₘ`, and the ambient unipotent factor is
`blockEmbed(diag Vₘ) · blockEmbed(regRep_ℝ μ)`.

So "Humbert-reduced ⟹ ambient Siegel-reduced" reduces to three bounds:

```text
|μ_{ij}|_v ≤ u  ⟹  |regRep_ℝ(μ_{ij})| bounded          [linear algebra, constant depends on ω]
Δ_{m,v}/Δ_{m,v'} ≤ K  ⟹  Vₘ and the ratios of Dₘ bounded  [Eₘ ≍ Δ_{m,v₀}·ΩᵀΩ]
Δ_{m,v} ≤ t Δ_{m+1,v}  ⟹  the ambient diagonal ordering    [across blocks]
```

The middle bound is the one with real content and it is **why the unit group enters**: without a
constraint on the *shape* of `Δₘ` the factor `Vₘ` is unbounded, and the shape is normalised by
replacing `b_m` by `ε b_m` for a unit `ε`, which sends `Δ_{m,v} ↦ σ_v(ε)² Δ_{m,v}`.  Dirichlet's unit
theorem — the unit lattice spans the trace-zero hyperplane — is exactly what makes the shape
normalisable.  This was not visible before computing the ambient Jacobi data.

The covering itself is then the potential descent, with

  `P(A) = ∏_{i=1}^{n} det(leadingBlock (i·d) A)`,

which is a function of the ambient form alone, is bounded below by `pow_le_det_leadingBlock` (F32),
is unchanged by `R`-shears (block unipotent, hence ambient unipotent by the block-major ordering) and
by unit rescalings, and is decreased by an `R`-swap when the `R`-Lovász condition fails.  The moves:

```text
R-shear  b_i ↦ b_i + α b_j (j < i), α ∈ R          size reduction = lattice rounding (ZSpan.floor)
unit     b_m ↦ ε b_m, ε ∈ R^×                       shape normalisation (Dirichlet)
R-swap   b_i ↔ b_{i+1}                              the descent step
```

```text
blockEmbed / orderRep / balanced subspace / the action      [PROVED]
Macbeath's criterion over an order                          [PROVED]
the finiteness half over an order                           [PROVED]
ambient Jacobi data of a block form                         [PROVED]
Gram–Schmidt over R ⊗ ℝ; the factorization A = Wᵀ E W       [OPEN]
size reduction (rounding), shape normalisation (Dirichlet)  [OPEN]
the R-Lovász swap and the potential descent                 [OPEN]
Humbert-reduced ⟹ ambient Siegel-reduced                    [OPEN]
SL_n(𝒪_F) finitely presented, F totally real                [OPEN]
```

## F49. Real embeddings diagonalise the regular representation `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/RealOrderEmbeddings.lean`

`RealOrderData R d` packages a `ℤ`-basis `ω` of the order together with `d` ring homomorphisms
`σ_v : R → ℝ` whose evaluation matrix `Ω_{v,k} = σ_v(ω_k)` is invertible.  That is the whole of
"totally real order of degree `d`" that the reduction theory needs — no `NumberField` machinery, and
in particular no `F ⊗ ℝ`.

- **`embMatrix_mul_entryRep`** : `Ω · ρ(α) = diag(σ_v α) · Ω`.  The proof is one application of
  `Basis.sum_repr` and `ℤ`-linearity of `σ_v`: the `k`-th column of `ρ(α)` is the coordinate vector
  of `α ω_k`, and `σ_v` of that is `σ_v(α) σ_v(ω_k)`.
- **`exists_diagonal_of_selfAdjoint`** : if `ρ(α)ᵀ B = B ρ(α)` for every `α ∈ R`, then
  `B = Ωᵀ diag(c) Ω` for some `c`.  Conjugating by `Ω` turns the hypothesis into "`C` commutes with
  `diag(σ_v α)` for all `α`", and the off-diagonal entry `(v,w)` is killed by any `α` with
  `σ_v α ≠ σ_w α` — which exists whenever `v ≠ w`, because otherwise rows `v` and `w` of `Ω` would
  coincide and `Ω` would be singular.  The spanning argument (that `{σ(α)}` spans `ℝ^d`) is not
  needed: a *single* separating basis element per pair of places suffices.

This is the coordinate description of the balanced forms:

  `A ∈ balancedSubspace  ⟺  every block of `A` is `Ωᵀ diag(c_{ij}) Ω``,

i.e. `A = Tr(H)` for a matrix `H` over `Fin d → ℝ` — the Humbert coordinates.  Combined with F48's
`blockJacobi_twist_form`, the ambient Jacobi data of such an `A` is now computable from `(μ, Δ)`
alone, which is what the "Humbert-reduced ⟹ ambient Siegel-reduced" step needs.

Next: assemble the block characterization for the whole form, run Gram–Schmidt on `H` place by place
(each place is an ordinary real `JacobiData nb`, so the existing machinery applies verbatim `d`
times), and then the descent.

## F50. The Humbert dictionary `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/HumbertCoordinates.lean`, `HumbertAmbientJacobi.lean`,
`HumbertPositivity.lean`

The symmetric space of `SL_n(R)` is now identified with `d` copies of the cone of positive definite
real `n × n` forms, and the ambient Jacobi data of a point is computed from that identification.

- **`blockUnembed`** inverts the flattening, so ambient identities can be read blockwise.
- **`humbertForm T H = blockEmbed (fun i j => Ωᵀ diag(H i j) Ω)`** for
  `H : Matrix (Fin n) (Fin n) (Fin d → ℝ)`.  `humbertForm_mem_balancedSubspace` and
  `exists_humbert_of_mem_balancedSubspace` say the balanced forms are **exactly** these; the second
  is F49 applied blockwise, using `blockEmbed_injective` to pass from the ambient identity
  `(orderScalar α)ᵀ A = A (orderScalar α)` to the block identity `ρ(α)ᵀ A_{ij} = A_{ij} ρ(α)`.
- **`humbertForm_factor`** : if `H i j v = (Jv v).form i j` for a family `Jv` of Jacobi data, one per
  embedding, then `humbertForm T H = Wᵀ E W` with `W = blockEmbed(ρ_ℝ μ)` unipotent upper triangular
  (`isUnipotentUpper_blockEmbed`: block upper unitriangular flattens to unipotent upper triangular,
  because the block-major ordering makes the blocks contiguous) and `E` block diagonal with blocks
  `Ωᵀ diag(Δ_m) Ω`.  The computation is the cancellation `(Ω⁻¹)ᵀΩᵀ = 1`, `ΩΩ⁻¹ = 1` and
  `diagonal_mul_diagonal`.
- **`humbertAmbient`** = `(blockJacobi Jm).twist (isUnipotentUpper_humbertUnipotent T Jv)`, with
  `humbertAmbient_form` proving its form is the Humbert form, `humbertAmbient_d` giving
  `d_{(m,k)} = (Jm m).d k` and `humbertAmbient_U` giving `U = blockEmbed(diag Uₘ) · W`.  So **the
  ambient Jacobi data of a Humbert form is explicit**, which is what the transfer to ambient Siegel
  bounds needs.
- **`posDef_humbert_place`** : positivity passes to the place components.  Congruence by
  `humbertUnscale = blockEmbed(diag Ω⁻¹)` strips `Ω`, leaving `blockEmbed (fun i j => diag (H i j))`,
  and `H_v` is the principal submatrix of that on the indices `(i, v)` — so `Matrix.PosDef.submatrix`
  finishes.  No quadratic-form computation is needed.
- **`exists_humbert_jacobi`** : every point of `orderCone` is `humbertForm T H` with each `H_v`
  positive definite, hence carries Gram–Schmidt data at every embedding.

State of the `𝒪_F` lane:

```text
blockEmbed / orderRep / balanced subspace / the action      [PROVED]
Macbeath's criterion over an order                          [PROVED]
the finiteness half over an order                           [PROVED]
ambient Jacobi data of a block form                         [PROVED]
real embeddings diagonalise the regular representation      [PROVED]
the Humbert dictionary and the ambient Jacobi data          [PROVED]
size reduction (rounding), shape normalisation (Dirichlet)  [OPEN]
the R-Lovász swap and the potential descent                 [OPEN]
Humbert-reduced ⟹ ambient Siegel-reduced                    [OPEN]
SL_n(𝒪_F) finitely presented, F totally real                [OPEN]
```

## F51. Rounding, the potential, and the action in Humbert coordinates `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/OrderRoundingPotential.lean`, `HumbertAction.lean`,
`OrderShear.lean`

- **`exists_round`** : there is `C` with `∀ x : ℝ^d, ∃ α ∈ R, ∀ v, |x_v − σ_v(α)| ≤ C`.  This is
  size reduction over an order, and it needs no lattice theory: put `y = Ω⁻¹x`, take `α = Σ round(y_k) ω_k`,
  and then `x − σ(α) = Ω(y − round y)` with `|y − round y| ≤ 1/2` entrywise.  (`ZSpan.floor` would
  also do it; this is shorter and avoids the `NumberField` dependency.)
- **`det_leadingBlock_humbertAmbient`** : the leading minor of a Humbert form at `i·d` is
  `(det Ω)^{2i} ∏_{m<i} ∏_v Δ_{v,m}`.  So the covolumes of the sublattices spanned by the first `i`
  basis vectors **over the order** — the quantities the descent has to decrease — are, up to the
  constant `(det Ω)²` per step, the products of the norms of the Gram–Schmidt diagonals.  The
  descent's potential is therefore the ambient potential of the integral theory restricted to the
  multiples of `d`, and its lower bound is `pow_le_det_leadingBlock` (F32) unchanged.
- **`humbertForm_congr`** : `ρ(N)ᵀ · humbertForm T H · ρ(N) = humbertForm T H'` with
  `H'_v = σ_v(N)ᵀ H_v σ_v(N)`.  **The action of `SL_n(R)` on its symmetric space is the diagonal
  action on `d` copies of the cone of positive definite real `n × n` forms.**  The proof is
  `embConj_diagonal` — `ρ(α)ᵀ (Ωᵀ diag(c) Ω) ρ(β) = Ωᵀ diag(σ(α) c σ(β)) Ω`, from F49's
  diagonalisation — summed over the two block indices with `sum_embConj`.
- **`humbertForm_shear`** : an elementary shear `1 + α E_{ji}` with `j < i` is `Matrix.transvection`,
  its embedding at each place is the transvection with coefficient `σ_v(α)`
  (`placeMatrix_orderShear`), it is unipotent upper triangular there
  (`isUnipotentUpper_transvection`), and so by the placewise description it **twists each of the `d`
  Gram–Schmidt data and changes none of their diagonals**.  Hence it leaves the potential fixed —
  exactly the role size reduction plays in the integral descent.

With `exists_round` supplying the coefficient, a shear can put `μ_{v,j,i}` inside a fixed bound at
*every* place simultaneously.  What remains of the covering:

```text
the size-reduction sweep (iterate the shear over the pairs j < i)   [OPEN]
shape normalisation of each Δ_m by units (Dirichlet)                [OPEN]
the R-Lovász swap and the potential descent                         [OPEN]
Humbert-reduced ⟹ ambient Siegel-reduced                            [OPEN]
SL_n(𝒪_F) finitely presented, F totally real                        [OPEN]
```

## F52. Size reduction over an order, and why the Lovász swap cannot terminate the descent `[PROVED / CORRECTION]`

`formal/GaloisForLFunctions/HTGeometry/OrderSizeReduction.lean`

- **`superShear k e`** is the shear `1 + Σ_i e_i E_{i,i+k+1}` supported on one superdiagonal; it is
  unipotent upper triangular, has determinant one over any commutative ring
  (`det_of_upperTriangular`), its embedding at each place is the real superShear of the embedded
  coefficients (`placeMatrix_superShear`), and `mul_superShear_apply` records its effect: entries at
  offset `≤ k` are unchanged, and the entry at offset `k+1` becomes `V_{ij} + e_i`.
- **`exists_orderSweep`** : with the rounding constant `C` of F51, one shear puts the whole
  superdiagonal of offset `k+1` inside `C` **at every embedding at once** — the coefficient is
  `round`ed against the vector of the `d` entries.
- **`exists_orderSizeReduction`** : iterating `nb` times, a single `N ∈ SL_n(R)` gives
  `|(U_v · σ_v(N))_{ij}| ≤ C` for all `i < j` and all `v`.

### The correction: the descent cannot be run by a Lovász swap

The integral descent (F32) terminates because a failed Lovász condition lets a swap decrease the
potential by a *fixed factor* `q < 1`, which is available because size reduction there gives
`|U_{ij}| ≤ 1/2 < 1`.  Over an order this fails, and the failure is not a matter of constants.

After size reduction the swap at `m` replaces `Δ_{v,m}` by `Δ_{v,m+1} + Δ_{v,m}δ_v²` with
`δ_v = μ_v − σ_v(α)`, so with `r_v = Δ_{v,m+1}/Δ_{v,m}` the potential drops by the factor
`∏_v (r_v + δ_v²)`.  For a definite contraction one needs `∏_v (r_v + δ_v²) < q < 1` **uniformly in
`r`**, hence `∏_v δ_v² < 1`, hence `inf_{α ∈ R} |N(μ − α)| < 1` for every `μ` — that is, `F` must be
**norm-Euclidean**.  Most totally real fields are not.  So no choice of the size-reduction constant
or of the Lovász threshold makes the swap contract, and `exists_terminal_of_contracting` cannot be
the termination mechanism over an order.  This is the precise reason Humbert reduction is harder
than LLL, and it was not visible before the shear computation above.

### The replacement: finiteness of Gram values

The termination input that does work, and that the corpus can already reach:

> **(FIN)** For a positive definite `A` on `ℤ^N` and `B > 0`, the set of values
> `{det(Cᵀ A C) : C an integral `N × k` frame}` inside `(0, B]` is **finite**.

Given (FIN), the potential `Pot(γ·A) = ∏_{i=1}^{n} det(leadingBlock (i·d) (γᵀAγ))` takes finitely
many values below `Pot(A)` — each factor is bounded above by `Pot/c^{n−1}` and below by `c`, using
ellipticity — so its **minimum over the orbit is attained**, and at a minimiser no move decreases it:
that is the terminal state, and the reduction bounds follow from it exactly as in the integral case.

(FIN) is provable from what is already in the tree, and the proof is the integral reduction theory
applied one dimension down:

```text
G := CᵀAC is positive definite; exists_siegel_inOrbit gives δ ∈ GL_k(ℤ) with
  δᵀGδ Siegel-(2,1); det is unchanged, so ∏ d_j = det G ≤ B.
pow_le_det_leadingBlock bounds each leading minor below by λ^j (ellipticity of A on ℤ^N),
  hence det_j ≤ B/λ^{k−j} and d_j = det_{j+1}/det_j ≥ λ^k/B.
So each d_i ≤ B/(λ^k/B)^{k−1}, and form_diag_le_siegel bounds A[Cδ e_i] ≤ c·d_i.
finite_latticePoints_le then confines the columns of Cδ to a finite set,
  and det(CᵀAC) = det((Cδ)ᵀA(Cδ)) is determined by them.
```

```text
size reduction over an order                                        [PROVED]
(FIN) finiteness of Gram values below a bound                       [OPEN]
the descent by minimisation of the potential                        [OPEN]
shape normalisation of each Δ_m by units (Dirichlet)                [OPEN]
Humbert-reduced ⟹ ambient Siegel-reduced                            [OPEN]
SL_n(𝒪_F) finitely presented, F totally real                        [OPEN]
```

## F53. (FIN): finitely many Gram values below a bound `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/ReducedDiagonalBound.lean`, `GramValueFiniteness.lean`

The termination input identified at F52 is now unconditional in Lean.

- **`prod_filter_lt_eq_det_leadingBlock`** identifies the head `∏_{m<i} d_m` of the diagonal product
  with the `i`-th leading minor, by transporting the product along `Fin.castLE` — the bridge between
  the `Finset.filter` bookkeeping of the Siegel estimates and the `leadingBlock` bookkeeping of the
  minor estimates.
- **`d_le_bound_of_siegel`** : for a Siegel-`(2,1)` datum with `lam^j ≤ det A_j` for all `j` and
  `det A ≤ B`, every `d_i` is at most `max 1 (2^{k²} B / lam^k)`.  The head of the product is at
  least `lam^k`, so the tail is at most `B/lam^k`; the Siegel ordering makes every tail factor at
  least `2^{-k} d_i`, so `d_i^{|tail|} ≤ 2^{k²} B / lam^k`; and an exponent at least one converts
  that into the bound on `d_i` itself.
- **`finite_intGram_values`** : for a positive definite `A` on `ℤ^N` and any `B`, the set

    `{det(Zᵀ A Z) : Z an integral N × k frame, the Gram matrix positive definite, det ≤ B}`

  is **finite**.  Given `Z`, `exists_siegel_inOrbit_det_one` (F46) produces `g ∈ SL_k(ℤ)` making
  `(Zg)ᵀA(Zg)` Siegel-`(2,1)` without changing the determinant.  Ellipticity of `A`
  (`exists_ellipticity`) plus integrality of the standard Gram matrix `(Zg)ᵀ(Zg)` give
  `lam^j ≤ det A_j` through `pow_le_det_leadingBlock` (F32) — and crucially `lam` depends only on
  `A`, not on `Z`, because the domination is transported through the frame by
  `dotProduct_congr_mulVec`.  Then `d_le_bound_of_siegel` bounds each `d_i`,
  `form_diag_le_siegel` (F45) bounds each diagonal entry of the Gram matrix, `intGram_diag`
  identifies that entry as the `A`-length of a column of `Zg`, and `finite_latticePoints_le`
  confines the columns to a finite set.  The determinant is a function of those columns.

This is exactly the finiteness that replaces the contraction factor.  With it, the potential

  `Pot(γ·A) = ∏_{i=1}^{n} det(leadingBlock (i·d) (γᵀAγ))`

has each factor equal to `det(intGram A C_i)` for the integral frame `C_i` of the first `i·d` columns
of `γ`, so each factor takes finitely many values below any bound, and — since the factors are
bounded below by ellipticity — so does the product.  **The minimum of the potential over the orbit is
therefore attained**, and a minimiser is the terminal state of the reduction.

```text
(FIN) finiteness of Gram values below a bound                       [PROVED]
the descent by minimisation of the potential                        [OPEN]
shape normalisation of each Δ_m by units (Dirichlet)                [OPEN]
Humbert-reduced ⟹ ambient Siegel-reduced                            [OPEN]
SL_n(𝒪_F) finitely presented, F totally real                        [OPEN]
```
