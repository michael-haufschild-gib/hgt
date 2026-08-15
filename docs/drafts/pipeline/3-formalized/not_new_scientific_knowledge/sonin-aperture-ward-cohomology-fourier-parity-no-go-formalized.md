# Formalization record: Sonin aperture Ward cohomology and Fourier-parity no-go

- **Stage:** 3-formalized
- **Scientific status:** `[FORMAL CLOSURE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:**
  `sonin-aperture-ward-cohomology-fourier-parity-no-go.md`
- **Lean modules:**
  - `formal/GaloisForLFunctions/RHTower/SoninApertureWardPotential.lean`
  - `formal/GaloisForLFunctions/RHTower/SoninApertureFourierParityNoGo.lean`
  - supporting energy theorem in
    `formal/GaloisForLFunctions/RHTower/SoninApertureWardCurvature.lean`
- **Umbrellas:** imported by `RHTower.lean` and `RiemannHypothesisSOTA2026.lean`.

## Formalized frontier closure

Lean proves, unconditionally:

1. aperture restriction curvature is an operator two-coboundary;
2. successive-layer Hilbert--Schmidt energy obeys exact four-aperture Bianchi conservation;
3. scalar curvature is coboundary of explicit base-aperture Ward potential;
4. base changes are exact vertex gauges;
5. symmetric aperture transition and Ward channel are Fourier-even;
6. bilateral forward-minus-inverse holonomy is Fourier-odd;
7. every Fourier-invariant complex-linear reader annihilates that holonomy;
8. equality of such reader with positive Ward energy is equivalent to literal flatness.

No `axiom`, `sorry`, `admit`, `opaque`, `unsafe`, RH premise, Xi-zero premise, numerical
computation, or external estimate is used.

## Frontier consequence

Do not again propose a Fourier-invariant linear relative trace as the RH-oriented reader of
bilateral aperture holonomy. Lean proves it is identically zero. The only surviving Suzuki reader
class is fibre-pointed and reflection-covariant between distinct fibres, not globally invariant at
one fibre. Current exact target is co-Poisson Berezin same-point sign on annihilator characters.
