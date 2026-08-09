# Formalized: Burnol holonomy / Cauchy divided-shift sector separation

- **ID:** `burnol-holonomy-cauchy-sector-separation-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `burnol-holonomy-cauchy-sector-separation.md` (same directory)

## Lean modules

| Module | Role |
|---|---|
| `GaloisForLFunctions.RHTower.BurnolHolonomyCauchySectorSeparation` | strict accretivity and both separation theorems |
| `GaloisForLFunctions.RHTower.BurnolDividedShiftPhysicalDissipativity` | accretivity identity and the fixed source atom (inputs) |
| `GaloisForLFunctions.RHTower.BurnolCoPoissonQuotientOrder` | Fourier-oddness of the compressed holonomy (input) |

## Formal theorem chain

1. `re_inner_burnolMellinDividedShift_pos` — strict accretivity: for `1/2 < Re ρ` and every nonzero
   even vector, `0 < Re ⟪f, A_ρ f⟫`.
2. `burnolMellinDividedShift_ne_bilateralApertureHolonomy` — the one-sided Mellin divided shift is
   never an uncompressed finite bilateral aperture holonomy.
3. `burnolMellinDividedShift_ne_compressedHolonomy` — the same for the quotient-compressed holonomy.

Both separations run through the same mechanism: Fourier oddness reverses the quadratic form along
the cosine orbit of the fixed sub-window source atom, whereas strict accretivity makes both orbit
values positive.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/BurnolHolonomyCauchySectorSeparation.lean` — clean.
- `#print axioms` on all three theorems: `propext`, `Classical.choice`, `Quot.sound` only.
- Imported by `GaloisForLFunctions.RHTower`.
