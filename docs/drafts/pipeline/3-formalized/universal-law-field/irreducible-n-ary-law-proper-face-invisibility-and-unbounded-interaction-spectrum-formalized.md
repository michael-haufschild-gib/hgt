# Irreducible `n`-ary law, proper-face invisibility, unbounded spectrum — Lean certification

- **ID:** ULF-IRR-1
- **Paper card:**
  `irreducible-n-ary-law-proper-face-invisibility-and-unbounded-interaction-spectrum.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveIrreducibleInteraction`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Reused corpus layer:**
  `GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.MinimalLawLeadingJet`
  (`MinimalLaw`, `MinimalLawEquiv`, `FirstNonzero`, `IsAbelian`, first-order invariance)

## Certified declarations

### The law

`InteractionCarrier N = (Fin N → ℝ) × ℝ` carries the `N` colours and the interaction-output line.
`interactionBracket N` is the alternating map

`ℓ_N (v₁, …, v_N) = det (Matrix.of fun i j => (v i).1 j) • z`,

built as `LinearMap.toSpanSingleton … |>.compAlternatingMap (Matrix.detRowAlternating.compLinearMap
(LinearMap.fst …))`.  `interactionBracket_colorGen` proves `ℓ_N (x₁, …, x_N) = z`, so
`interactionBracket_ne_zero` holds.  `bracketFamily N r` is the whole operation family: the bracket
in arity `N` (`bracketFamily_self`) and zero in every other arity (`bracketFamily_of_ne`), obtained
by `AlternatingMap.domDomCongr` along `finCongr`, so no dependent cast on linear maps is needed.

### Theorem 2.1 — minimality and irreducibility

`interactionBracket_fst` proves that every bracket output has zero colour component, and
`bracketFamily_eq_zero_of_fst_eq_zero` that a single colourless input annihilates the bracket.
Together they give `bracket_composite_eq_zero`: *every* composite, of any two arities and in any
slot, is zero.  Consequently `linfty_identity` proves that any signed sum of composites vanishes —
so every generalized Jacobi identity holds whatever the Koszul sign convention is, and the family
really is an `L∞` structure.  `bracketFamily_zero_and_one` records that the law is uncurved and
minimal.

`colorFace N S` is the face spanned by `z` and the colours in `S`.
`bracketFamily_comp_face_eq_zero` proves that restricting any operation to a proper face is zero: a
missing colour is an identically zero column of the defining determinant.  `faceBracketFamily` is
the corestricted face operation family, `faceLaw` the induced minimal law, and
`faceLaw_isAbelian` / `faceLaw_isAbelian_of_card_lt` prove that every face with fewer than `N`
colours is abelian.

`irreducibleLaw N hN` packages the operations as a `MinimalLaw` on `⋀[ℝ]^r (InteractionCarrier N)`.
`irreducibleLaw_not_isAbelian` proves the total law is not abelian, and `not_isAbelian_of_equiv`
transports this along any `MinimalLawEquiv`: no formal-law equivalence takes the law to an abelian
one, i.e. it is not homotopy abelian.

### Corollary 2.2 — exact interaction order

`irreducibleLaw_firstNonzero` proves `FirstNonzero N`, so the interaction order is exactly `N`.
`interactionOrder_eq` shows any equivalent law has the same first nonvanishing arity.
`arityTruncation` is the observer that discards every operation above a given arity, and
`arityTruncation_isAbelian` proves that truncating below `N` reports an abelian law.
`irreducible_properFace_invisible` bundles the four conclusions.

### Theorem 2.3 — unbounded interaction spectrum

`TowerCarrier = ∀ m : ℕ, InteractionCarrier (m + 3)` is the product of one irreducible block of
every order at least three, and `towerBracket r = AlternatingMap.pi …` is the product law.

- `towerBracket_composite_eq_zero` — the product law squares to zero;
- `towerBracket_apply_eq_zero_of_le` — an arity-`M` observer annihilates every block of order
  above `M`; `towerBracket_mem_towerHead` says all its outputs lie in the visible head;
- `zTail M` embeds the product of the output lines of all blocks of order above `M`;
  `zTail_injective`, `instInfiniteTailIndex`, and `zTail_range_disjoint_towerHead` prove the
  invisible tail is an infinite independent family meeting the visible head only at zero, and
  `towerBracket_eq_zero_of_mem_zTail` that the tail is annihilated by every arity-`M` operation;
- `not_locallyCompactSpace_pi_real` — the full interaction-output space `ℕ → ℝ` with its product
  topology is not locally compact: any neighbourhood of a point leaves some coordinate entirely
  unrestricted, so the projection of a compact neighbourhood would make `ℝ` compact.

`unbounded_interaction_spectrum` bundles these five conclusions.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveIrreducibleInteraction.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveIrreducibleInteraction
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All checks passed with no warnings.  `#print axioms` on the Jacobi identity, the composite
vanishing, the bundled irreducibility theorem, the homotopy-abelian transport, the order
invariance, the spectrum capstone, and the non-local-compactness reports only `propext`,
`Classical.choice`, and `Quot.sound`.  No project axiom, placeholder, hypothesis interface, or
unresolved theorem premise is used.

## Exact field consequence

Proper-face blindness does not identify the global ontology.  Here a global law exists and is a
genuinely higher operation, invisible to every observer that keeps fewer colours or lower arity;
in the parity-contextual model (`ULF-CTX-1`) the same blindness comes with no global law at all.
Any universal field must retain arity support as an invariant separate from tangent dimension, and
the unbounded arity tower supplies observer escape through a non-locally-compact output space.
