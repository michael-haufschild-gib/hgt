# Localized optimal recurrence-capacity law

- **Status:** formalized
- **Lean module:** `GaloisForLFunctions.RHTower.FiniteLocalizedOptimalCapacityLaw`
- **Claim class:** `[LEAN-PROVED] [BRIDGE]`

## Result

For a normalized nonnegative finite spectral packet, nonempty retained
support \(S\), and tail mass at most \(\alpha\), the clique on \(S\) with
isolated exterior sectors is feasible at deviation
\[
 \varepsilon=4\alpha+\frac{4\pi}{Q+1}.
\]
Its exact graph capacity is \(|S|-1\). Therefore the canonical optimal
capacity satisfies
\[
 {\cal C}_{\varepsilon}(Q)\le |S|-1.
\]

## Formal declarations

- `finiteSectorUnionCoefficientMass_eq_finiteUnionCoefficientMass`
- `finiteSectorSelectedDirectedMass_eq_finiteSelectedDirectedMass`
- `finiteSectorOmittedDirectedMass_eq_finiteOmittedDirectedMass`
- `finiteLocalizedSpectralSupport_sectorGraphCapacity`
- `finiteLocalizedSpectralSupport_sectorBudget_le`
- `finiteLocalizedSpectralSupport_sectorTarget_feasible`
- `finiteLocalizedSpectralSupport_optimalCapacity_le`

## Verification

Direct foreground compilation passed. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Boundary

The result is an upper bound on canonical certified capacity. It does not
claim that every localized spectrum has matching lower capacity.
