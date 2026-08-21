# Affine formation current and the four-organ Bianchi law — Lean certification

- **ID:** ULF-FHM-2
- **Paper card:** `base-preserving-affine-formation-current-and-four-organ-bianchi-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.AffineFormationCurrent`
- **Depends on:** `GaloisForLFunctions.HTGeometry.SplitFormationCornerFlatness` (ULF-FHM-1)
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

## §1–§2 Affine vertical normal form (Theorem 2.1)

`BasePreserving` is `(AFC.4)` — only recovery is preserved, the section is not.
`formationCurrent` and `affineTransport` are `(AFC.5)`; both are proved to land in `ker p`.
`splitChart_basePreserving` is **`(AFC.6)`** and `affine_normal_form_unique` its uniqueness
clause.  `formationCurrent_eq_zero_iff` is **`(AFC.7)`** and
`formationCurrent_and_transport_eq_zero_iff` is **`(AFC.8)`**.  The split chart itself
(`splitChart`, `splitAssemble`, `recover_form`) is inherited from ULF-FHM-1.

## §3 Semidirect composition (Theorem 3.1)

`BasePreserving.comp`, `affineTransport_comp` and `formationCurrent_comp` are **`(AFC.9)`**:
the inner current is transported by the outer vertical law *before* it is added.

## §4 Joint triangle defect (Theorem 4.1)

`currentDefect` and `transportDefect` are `(AFC.11)`; `recover_comp_affineDefect` is **`(AFC.13)`**
and `splitChart_affineDefect` is **`(AFC.12)`**: the joint defect is purely vertical and splits
into a generated part and a transported part.

## §5 Four-organ Bianchi identities (Theorem 5.1)

`bianchi_transport` is **`(AFC.15)`** and `bianchi_current` is **`(AFC.16)`**.  Both are stated as
*formal identities in arbitrary currents and transports*, which is strictly stronger than the
card's statement for comparison-derived data, and makes the load-bearing mixed term
`Λ_{ℓkj} a_{ji}` explicit in the statement.

## §6 Finite diagonal/reset realization (Theorem 6.1)

`marginalRecovery` is `(AFC.17)`; `diagSection` and `resetSection` are `(AFC.18)`, with
`marginalRecovery_diagSection` and `marginalRecovery_resetSection` proving both are sections.
`basePreserving_id` makes the ambient identity a comparison from the diagonal chart to the reset
chart; `affineTransport_id_realization` and `formationCurrent_id_realization` are **`(AFC.19)`**;
`formationCurrent_at_weight` is **`(AFC.20)`**; `formationCurrent_reverse_add` is the exact signed
cancellation of the reverse comparison.

The three exact shadows:

* `totalVariation_current` — **`(AFC.21)`**: `TV(Δ_q, q⊗q) = 1 − Σ q_a²`;
* `relativeEntropy_current` — **`(AFC.22)`**: `D(Δ_q ‖ q⊗q) = H(q)` (with the `0 log 0 = 0`
  convention supplied by `Real.log 0 = 0`);
* `diagonalState`, `diagonalState_mulVec_single`, `vonNeumannEntropy_diagonalState` —
  **`(AFC.23)`**: the weight entries are eigenvalues of the diagonal density state, whose spectral
  entropy is `shannonEntropy q`.

Together these are the card's Loop D refutation: the signed currents cancel exactly
(`formationCurrent_reverse_add`) while the positive shadows do not.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/AffineFormationCurrent.lean
```

Elaborates with no errors and no warnings.  `#print axioms` on all 35 public declarations reports
only `propext`, `Classical.choice`, `Quot.sound`.  The module is imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField` and by `GaloisForLFunctions.HTGeometry`.

## Still open (not proved theorems)

The card's last two gates: a literal arithmetic three-organ comparison, and a source-generated
positive properness law.  Both are construction burdens stated as future work.
