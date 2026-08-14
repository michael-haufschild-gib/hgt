# Positive-even Laplace escape finite core — formalized

- **ID:** ULF-EAEM-2-LEAN
- **Stage:** 3-formalized
- **Paper parent:**
  `../../../2-fully-proven/universal-law-field/exponential-admission-escape-mechanics/positive-even-schwartz-off-axis-zero-density-and-formation-properness-no-go.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/ConstitutivePositiveEvenLaplaceEscape.lean`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

- `positiveEvenTwoShellLaplace` — even two-shell bilateral-Laplace response;
- `positiveEvenTwoShellLaplace_weights_pos` — both cancellation weights are strictly positive;
- `positiveEvenTwoShellLaplace_offAxis_zero` — exact cancellation at every `a + pi I`;
- `positiveEvenTwoShellLaplace_explicit_offAxis` — closed witness at `1 + pi I`.

## Verification

Exact module source was first elaborated in scratch with

```text
lake env lean /tmp/ConstitutivePositiveEvenLaplaceEscape.lean
```

and exited successfully. The verified declarations were then copied into the leaf module and the
leaf import was wired into `UniversalLawField.lean`. Per current workspace instruction, no leaf,
area, umbrella, or project build was run afterward.

## Scope

Lean certifies the exact finite positive cancellation mechanism. The Gaussian smoothing,
remote-packet Schwartz convergence, and zero-insertion density theorem remain paper-proved and are
not claimed as Lean-certified by this card.
