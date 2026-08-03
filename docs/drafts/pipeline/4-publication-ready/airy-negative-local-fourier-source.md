# Airy negative local-Fourier source

- **ID:** `airy-negative-local-fourier-source`
- **Stage:** 4-publication-ready
- **Type:** theorem infrastructure
- **Knowledge label:** `[LITERATURE THEOREM] [NEW LEAN FORMALISATION] [FORMALISED] [PUBLICATION READY]`
- **Source boundary:** Hiroe’s negative dual-Puiseux branch supplies historical context; operator,
  Laurent-coordinate, contact, and finite-resolution statements used by the manuscript are proved
  internally.

## Closed claim

For every Airy characteristic step `R > E` with canonical numerator `beta=R+E`:

1. the first Weyl algebra over `ℂ` is realized as the quotient of the free associative algebra by
   `D X - X D - 1` and acts by differentiation/multiplication on `ℂ[X]`;
2. the Fourier automorphism `X ↦ D`, `D ↦ -X` descends to that quotient and satisfies

   ```text
   F(D^R-X^E)=(-X)^R-D^E;
   ```

3. for a normalized Laurent leading term `t^(-(R+E))u(t)`, `u(0)=1`, the local Fourier coordinate
   has order `-E`, its reciprocal has order `E`, and

   ```text
   t^E u(t)^(-1) = phi(t^E)
   ```

   for a tangent Laurent automorphism `phi`;
4. `phi` and its inverse preserve every pairwise Laurent contact and the complete threshold
   hierarchy;
5. applying this exact package at each successive characteristic tail gives a finite strictly
   decreasing rank trace ending at one, with zero loop at every suffix.

The manuscript does not assert a general analytic Fourier equivalence for arbitrary meromorphic
connections or that one generalized-Airy principal operator stores every lower Stokes coefficient.

## Gates

- [x] 0 → 1: exact source formula and anti-theatre failure modes isolated
- [x] 1 → 2: complete paper proof for stated operator/Laurent/contact package
- [x] 2 → 3: unconditional Lean theorems, direct checks, targeted builds, axiom audit
- [x] 3 → 4: manuscript trace and final hostile review accept dependency closure

## Anti-theatre closure

Rejected proxies were not used. Development contains:

- actual free noncommutative operator words;
- actual polynomial operator semantics and proved Weyl commutator;
- actual two-sided quotient and descended Fourier automorphism;
- actual polynomial gauge automorphisms;
- actual Laurent series, power-series units, formal inversion, valuation, and contact hierarchy;
- exact recursive characteristic-tail resolution whose rank trace is proved equal to the
  characteristic ramification trace.

The final theorem does not define the rank drop as a field of a certificate. Rank `E` appears
independently as the order of the reciprocal transformed coordinate and as the derivative degree
in the Fourier image.

## Formal sources

- `formal/GaloisForLFunctions/HTGeometry/StokesWeylFourierSource.lean`
- `formal/GaloisForLFunctions/HTGeometry/StokesLaurentFourierSource.lean`
- `formal/GaloisForLFunctions/HTGeometry/StokesFormalUniformizer.lean`
- `formal/GaloisForLFunctions/HTGeometry/StokesFormalContactInvariance.lean`
- `formal/GaloisForLFunctions/HTGeometry/StokesNegativeFourierContactTransport.lean`
- `formal/GaloisForLFunctions/HTGeometry/StokesNegativeFourierResolution.lean`

Principal capstones:

- `WeylFourier.fourier_generalizedAiryOperator`
- `Characteristic.airyTower_negativeFourier_exact_uniformizer`
- `Characteristic.airyTower_negativeFourier_contact_transport`
- `Characteristic.airyTower_exact_negativeFourier_resolution`

All are wired into `GaloisForLFunctions.HTGeometry`.

## Verification

- Direct `lake env lean` checks passed.
- Targeted module builds passed.
- Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`; no project axiom.
- Final manuscript proof and hostile review use exactly this scope.
