# Centered-flow countercharacter erasure and relative curvature — formalization certificate

- **Route:** L
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Paper theorem:**
  `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/deninger-centered-flow-countercharacter-relative-curvature-no-go.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/DeningerCenteredFlowCountercharacterRelativeCurvatureNoGo.lean`

## Exact formalized result

The canonical centered-flow clock countercharacter is the inverse of the Deninger half-density
mate gain:

```text
deningerCenteredFlowClockCountercharacter_eq_mateGain_inv
```

It equals the previously constructed Xi centered-flow source countercharacter at time `log n`:

```text
deningerCenteredFlowClockCountercharacter_eq_xi
```

Critical reflection inverts both characters:

```text
deningerCenteredFlowClockCountercharacter_reflection
deningerHalfDensityMateGain_reflection
```

Absolute covariant countertransport has gain one, equals flat affine top-conormal transport, and
has identically zero composition curvature:

```text
deningerCenteredFlowCountertransportedGain_eq_one
deningerCenteredFlowCountertransportedFramedTransport_eq_affine
deningerCenteredFlowCountertransportedFramedCurvature_eq_zero
```

The raw-to-flat relative reduced curvature retains the detector, and source/reflection
polarization recovers exact tensor-square mate curvature:

```text
deningerCenteredFlowRelativeReducedCurvature_eq
deningerCenteredFlowRelativeReducedCurvature_reflection_sub_source
```

At forced degree six it is the actual ordered `(2,3)` Gamma/Calderón--Witt coefficient:

```text
deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_relativeCountertransportCurvature
```

The two capstone no-go theorems prove that on every off-critical Xi fibre both absolute
countertransported curvatures vanish while actual Gamma coefficient remains nonzero; any
observation factoring through only those two absolute curvatures and vanishing at `(0,0)` misses
actual coefficient:

```text
deningerCenteredFlow_absoluteErasure_not_coefficientFaithful
deningerCenteredFlow_absoluteCurvatureObservation_ne_gamma
```

## Scientific delta

Covariant centered-flow conservation is not candidate singular Stokes annihilator. Its source
countercharacter gauges framed mate curvature flat at every parameter and therefore erases
off-critical Gamma provenance. Actual detector belongs to relative raw-to-covariantly-flat
mapping-cone class, whose reflection polarization is exact (K_6).

## Exact remaining core

`[RELATIVE_COUNTERCHARACTER_STOKES_ANNIHILATION]`

Construct literal preclosure relative exact couple for raw/countertransported pair; land relative
Bockstein coefficient-faithfully in completed Xi Green incidence before diagonal sewing; prove
source-derived arithmetic boundary law annihilates polarized relative class without assuming mate
curvature vanishing, countercharacter triviality, static capacity, or RH.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/DeningerCenteredFlowCountercharacterRelativeCurvatureNoGo.lean`: PASS.
- `lake build GaloisForLFunctions.RHTower.DeningerCenteredFlowCountercharacterRelativeCurvatureNoGo`: PASS; targeted module only, no full build.
- `#print axioms` on all headline and capstone theorems: only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Forbidden-token audit for `sorry`, `admit`, `axiom`, `opaque`, and `unsafe`: clean.
- `git diff --check` on every touched file: clean.
- Umbrella import present in `GaloisForLFunctions/RHTower.lean`.
- Global `scripts/formal_tools.py lint` currently fails on unrelated concurrent unreachable modules
  (CCM rational-adelic, cyclic-bar/cyclic-module, Deninger retract, invariant crossed-product,
  real-corona, and self-dual-sector files). It does not flag this module, which is reachable from
  the Route-Tower umbrella.
