# Proper-face matching map, four phases, total-law defect — Lean certification

- **ID:** ULF-MATCH-1
- **Paper card:**
  `proper-face-matching-map-four-phase-and-total-law-defect-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutivePolyscopicMatching`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Reused corpus layers:**
  `HTGeometry.ConstitutiveIrreducibleInteraction` (ULF-IRR-1),
  `HTGeometry.ConstitutiveParityContextuality` (ULF-CTX-1)

## Chart

The card is written in the infinity-category of spaces.  Neither mathlib nor the corpus carries
infinity-categories, so the certification is in the **0-truncated chart**: shadows are sets, the
proper-face matching object is the ordinary limit, the realization space is the ordinary fibre,
`(-1)`-truncated is injectivity and `(-1)`-connected is surjectivity.  Every numbered statement of
§2 has an exact 0-truncated form and all of them are certified; Corollary 2.4's higher homotopy is
outside the chart and its `π₀` content — realizability and multiplicity — is certified.

## Certified declarations

### Setup

`LawDiagram I` is a contravariant assignment of a law shadow to every observer face with functorial
restrictions; `ProperFaceDatum X` is the limit over proper faces (a compatible family);
`matchingMap X` is the restriction of a total law; `Realizations X m` is its fibre.

### Theorem 2.1 — realizability and ambiguity are fibres of one map

- `realizations_nonempty_iff` — a compatible proper-face datum is realizable iff its realization
  space is nonempty;
- `realizations_subsingleton_iff` — its realization is unique iff the realization space is a
  subsingleton;
- `matchingMap_bijective_iff` — the matching map is a bijection iff every compatible proper-face law
  has a unique total law, the 0-truncated form of (MM.5);
- `matchingMap_injective_iff`, `matchingMap_surjective_iff` — injectivity and surjectivity are
  exactly "every fibre is a subsingleton" and "every fibre is nonempty".

### Theorem 2.2 — four polyscopic phases

`Reconstructible`, `Contextual`, `Interacting`, `Mixed` are defined by the two independent
properties.  `four_phases` proves they are exhaustive and `phases_pairwise_disjoint` that they are
pairwise exclusive.  `DiagramEquiv` is an objectwise equivalence of diagrams, `DiagramEquiv.datum`
the induced equivalence of matching objects, and `phase_invariance` proves injectivity and
surjectivity of the matching map are invariant under it — hence so is the phase.

### Corollary 2.3 — kernel/cokernel shadow

`matching_kernel_cokernel` certifies the linear chart: the four-term sequence
`0 → ker μ → V → W → W ⧸ range μ → 0` is exact (`range (ker μ).subtype = ker μ` and
`range μ = ker (mkQ (range μ))`), the kernel vanishes iff the matching map is injective — no hidden
interaction — and the cokernel vanishes iff it is surjective — no contextual obstruction.

### Native realizations

`totalOnlyDiagram I A` is the diagram whose proper-face shadows record only satisfiability and whose
total law object is `A`; its matching object is a nonempty subsingleton.

- **Interaction phase.**  `scaledBracket_face_eq_zero` proves that scaling the irreducible `N`-ary
  bracket by any real amplitude leaves every proper colour face the zero law, and
  `scaledBracket_injective` that distinct amplitudes give distinct total laws.
  `interactionDiagram_isInteracting` then certifies the interaction phase: surjective, not
  injective.
- **Contextual phase.**  `properFace_satisfiable` records that every proper observer face of a
  connected parity context system is satisfiable for an arbitrary charge, and
  `contextualDiagram_isContextual` certifies that under an odd total charge the total-law object is
  empty, so the matching map is injective and not surjective.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutivePolyscopicMatching.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutivePolyscopicMatching
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All checks passed with no warnings.  `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound` (several statements need only `propext` and `Quot.sound`).  No project axiom,
placeholder, hypothesis interface, or unresolved theorem premise is used.

## Correction to §4.1 of the paper card

The card's §4.1 asserts that the parity Čech diagram has a nonempty proper-face matching object with
an empty realization fibre.  With the definitions of §1 that is not the case: the poset of proper
subsets contains the maximal faces `V \ {v}`, and compatibility across two of them already forces
every context equation, so the limit over proper faces coincides with the global law object and the
naive subset diagram is *reconstructible*, not contextual.  The contextual phase is instead realized
by taking the shadow of a proper face to be its satisfiability, which is exactly what ULF-CTX-1
supplies; that is the certified `contextualDiagram_isContextual`.  The correction is recorded in
§8 of the paper card.

## Exact field consequence

Realizability failure and hidden multiplicity are the two independent coordinates of one map, so no
scalar total obstruction can express both: a proof that all proper observer faces are consistent
constrains neither total realizability nor uniqueness.  In the linear chart the two coordinates are
literally the cokernel and the kernel of the matching map.
