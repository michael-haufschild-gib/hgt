# Clock geometry and conservation do not force Einstein dynamics

- **ID:** `clock-geometry-conservation-forces-einstein-dynamics`
- **Stage:** 5-failed
- **Killed route:** infer Einstein equation from complete clock reconstruction, Bianchi/Jacobi
  consistency, and conserved but otherwise unspecified stress-energy
- **Parent:** `../1-in-progress/quantum-clock-compass-chronodromy-law.md`
- **Formal survivor:** `../3-formalized/clock-dynamics-underdetermination.md`

## Exact obstruction

For every clock-reconstructed metric `g`, define

```text
T_eff = kappa^(-1) (G[g] + Lambda g).
```

Then contracted Bianchi plus metric compatibility makes `T_eff` conserved, and Einstein equation
holds identically. Modified-gravity corrections can likewise be shifted between geometric and
source sides unless matter source is independently fixed. Therefore:

```text
complete clock geometry + conservation
  does not identify gravitational dynamics.
```

Hojman--Kuchař--Teitelboim uniqueness does not repair this route without importing its canonical
phase space, embeddability/path-independence, locality, time-reversibility, and degree-of-freedom
assumptions. Lovelock uniqueness likewise needs a local metric-only natural tensor with bounded
derivative order. Those are dynamics assumptions, not consequences of clock tomography.

## Strongest positive survivor

The correct observable is not one reconstructed spacetime but the **chronometric intervention
functor**:

```text
independently calibrated matter-source intervention
  -> change of complete clock observable net.
```

Dynamics is the law of this source-to-clock map. Geometry is its state variable. A viable
clock-origin theorem for GR must prove that operational locality, source independence, and
clock-frame democracy make this interventional map equivalent to Einstein response, or else
classify the modified-gravity alternatives by their extra clock poles, characteristics, or
polarizations.

## Status

`NO-GO CLOSED; POSITIVE SURVIVOR FORMALIZED.` The algebraic effective-source theorem is
unconditional in
`formal/GaloisForLFunctions/HTGeometry/ClockDynamicsUnderdetermination.lean`.

