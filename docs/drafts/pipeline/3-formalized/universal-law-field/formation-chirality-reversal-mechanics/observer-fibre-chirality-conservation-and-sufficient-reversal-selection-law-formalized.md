# Observer-fibre chirality conservation and sufficient reversal — Lean certification

- **ID:** ULF-FCRM-2
- **Paper card:** `observer-fibre-chirality-conservation-and-sufficient-reversal-selection-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveObserverFibreChirality`,
  `GaloisForLFunctions.HTGeometry.KLFactorizationSufficiency` (new)
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

## Certified declarations

### Theorem 2.1 — exact observer-fibre conservation

`klChirality`, `observerFibreChirality`, `klChirality_observer_conservation`.  The setting is fully
measure-theoretic: arbitrary measurable spaces, `MeasureTheory.klDiv`, no finiteness of the source
space.

### Theorem 2.2 — serial observer-current composition

`observerFibreChirality_comp`, together with the exact conditional-KL identification
`observerFibreChirality_eq_conditionalDifference` through the standard-Borel disintegration.

### Theorem 3.1 and Corollary 3.2

`observerFibreChirality_pos_of_reversal`, `observerFibreChirality_eq_source_of_reversal`,
`observerTower_chirality_conservation`, `observerTower_chirality_eq_sum_of_terminal_zero`.

### Theorem 4.1 — sufficient reversible observation selects zero chronology

`IsKLPairSufficient`, `observerFibreChirality_eq_zero_of_pairSufficient`,
`klChirality_eq_zero_of_sufficient_reversal`, `klChirality_eq_zero_of_sufficient_reversal_left`,
`StrictKLChronology`, `SufficientReversalComparison`, `sufficientReversalSelection`.

### Section 5 — the sufficient-statistic reduction (new module)

Mathlib has no sufficiency theorem for `klDiv`.  `KLFactorizationSufficiency` supplies it:

- `map_withDensity_comp` — pushing a `q`-factored density through `q` gives the density itself on
  the observer space, `(R.withDensity (g ∘ q)).map q = (R.map q).withDensity g`.  This is exactly
  the card's computation `q_*P(B) = ∫_B g d(q_*R)`;
- `klDiv_map_eq_of_density_comp` — hence `D(P‖R) = D(q_*P‖q_*R)` whenever `dP/dR` factors through
  `q`.  Proved through `klDiv_eq_lintegral_klFun_of_ac` and `lintegral_map`: both sides are
  literally the same integral of `klFun ∘ g`;
- `isKLPairSufficient_of_density_comp` and `observerFibreChirality_eq_zero_of_density_comp` — the
  two-sided statement, which is the card's "mutual absolute continuity applies the same argument to
  `dR/dP = 1/(g∘q)`";
- `esscherLaw`, `esscherLaw_eq_withDensity_comp` — **(OFCC.11)**: two members of an exponentially
  tilted family differ by the density `(Z(t)/Z(s))·e^{(t−s)Q}`, which factors through `Q`;
- `esscher_isKLPairSufficient` — the tilting statistic is Kullback–Leibler pair-sufficient for
  every pair of members, on arbitrary (not necessarily finite or discrete) source spaces.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveObserverFibreChirality.lean
lake env lean GaloisForLFunctions/HTGeometry/KLFactorizationSufficiency.lean
```

Both elaborate clean.  `#print axioms` on all eleven chirality declarations and all six
factorization declarations reports only `propext`, `Classical.choice`, `Quot.sound`.  Both modules
are imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Cited, not reproved

`(OFCC.13)` — the positive-jump chronology equivalence `s < t ↔ D(P_s‖P_t) > D(P_t‖P_s)` — is
imported from the parent card and appears in Lean as the `StrictKLChronology.strict` field, exactly
the interface the card describes.  Building the abelian-zeta instance of that interface is the
card's remaining construction gate, not a proved statement of this card.
