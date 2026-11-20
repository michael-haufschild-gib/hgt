# Three-card formalization loop (Metzler, cutoff gap, Hawking–Page)

- **ID:** three-cards-formalization-loop-2011
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Statement:** Formalize unconditionally every proven theorem of the three cards below and move them to 3-formalized.

## Cards
1. 2-fully-proven/trans-metzler-weil-positivity.md — programme `TransMetzlerWeilPositivity`.
2. 2-fully-proven/arithmetic-counting-positive-density-exact-cutoff-gap.md — `ArithmeticCountingPositivity/PositiveDensityTransfersTheExactCutoffGap.lean`.
3. 2-fully-proven/arithmetic-hawking-page-phase-and-ads-modular-horizon-resolution.md — `CausalReflection/ArithmeticHawkingPagePhaseStructure.lean`, `BlackHoleRingdown/PrimeTwoDeformedApertureLogTwoTest.lean`.

## Gaps (card claim without a Lean theorem)
- [ ] G1 (card 1, Part IV.1): exact Fejér SOS identity, Toeplitz floor `-3/2`, public Hilbert floor `-1/2`, center-kernel floor `-Σ n x_n²`.
- [ ] G2 (card 1, Q1.3): finite off-line support ⇒ `weilQuad ≥ 0` on a coefficient subspace of codimension `≤ #rightZeros`.
- [ ] G3 (card 1, Q1.4): linear-in-`c` lower bound `|Wsummand| ≥ κ c ‖x‖² ∫g²` at a complex off-line zero, `x_n = cos(γ₀ log n)`.
- [ ] G4 (card 3, step 4): `μ` is `C^{1,1}_loc` on `(0,∞)` (locally Lipschitz derivative); requires a locally uniform transverse gap.
- [ ] Wiring: `PrimeTwoDeformedApertureLogTwoTest` and `ArithmeticHawkingPagePhaseStructure` into their umbrellas; direct import of the cutoff-gap module.
- [ ] Final audit: one foreground `lake --old env lean` per module + headline `#print axioms`.

## Covered (claim → Lean)
See each card's Lean section once moved.
