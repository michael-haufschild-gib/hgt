# Hecke correction of the actual scattering core

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `MayerScattering/HeckeScatteringBoundaryCorrection.lean`.

For `Re s>0`, `Im s>0`, set `q=2^(−2s)` and `c=2ζ(2s−1)/(2s−1)`. The actual finite-energy PM core satisfies

`T₂(core_s)(1)−(1+2q)core_s(1)=−2qζ(2s)+c(1−4q)`.

At every upper Mayer resonance this defect is nonzero, including resonances on `Re s=1/4`.
Thus the completed-period eigenvalue is not the action of raw four-branch Hecke on the actual PM core basis.

## Proof

On the period segment, the core is the complete period minus its zeta-axis term and scattering-power pair. At `a=1`, the period's three-term equation cancels the period values in the four Hecke branches. The remaining elementary powers give the displayed correction.

At a resonance, `ζ(2s)=0`; `ζ(2s−1)≠0` and `2s−1≠0`, so `c≠0`. Since `Re s<1/2`, `|q|=2^(−2 Re s)>1/2`, hence `1−4q≠0`.

## Lean

- `hecke_mayerPeriodCore_at_one`: exact correction.
- `hecke_mayerPeriodCore_at_one_ne`: nonvanishing at every upper resonance.

Final individual check passed; both endpoints depend only on `propext`, `Classical.choice`, `Quot.sound`. Imported by `RenormalizedIntersectionTheory.lean`.

## Positive survivor

The exact correction identifies the missing boundary channel. The [completed-period Hecke law](f2-global-lewis-hecke-eigenvalue.md) and [window Mellin correspondence](f2-hecke-window-mellin-correspondence.md) remain valid; assigning their eigenvalue directly to the core basis does not. The finite core realization must transport coefficients with this distinction intact.
