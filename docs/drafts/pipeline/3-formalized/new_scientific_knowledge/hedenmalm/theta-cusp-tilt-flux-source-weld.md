# Literal theta-cusp source realizes the global tilt-flux carrier

Status: Lean-formalized, unconditional source theorem. `[NOVELTY-PLAUSIBLE]`. Does not prove RH.

## Formal theorem package

The completed theta-cusp density obeys, for every real `M` and `x`,

```text
thetaCuspFullSource x
  <= thetaEnvelopeUpper * exp((|M|+5)^2/24) * exp(-M|x|).
```

It therefore defines the literal `ThetaSource` named `thetaCuspTiltSource`. Its bilateral Laplace
transform satisfies on the whole complex plane

```text
bilateralLaplace thetaCuspTiltSource w = xiCent w.
```

Thus its source Bezoutian is the centered-Xi Bezoutian and the abstract neutral tilt-flux RH
criterion specializes without any remaining source-construction hypothesis.

## Why this is progress rather than a restatement

The decay theorem is source-side and unconditional. The global transform theorem composes two
previously disconnected formal developments: the later all-plane theta Fourier--Laplace theorem
and the earlier abstract tilt-flux carrier. It discharges a frontier-map open construction gate.
The remaining flux-sign law is explicitly retained and is formally equivalent to RH.

## Lean source

`formal/GaloisForLFunctions/RHTower/ThetaCuspTiltFluxSourceWeld.lean`

Verification:

- direct source check passed with `lake env lean`;
- exact target build passed with
  `lake build GaloisForLFunctions.RHTower.ThetaCuspTiltFluxSourceWeld`;
- `#print axioms` for the pointwise envelope, global transform weld, and specialized RH criterion
  reports only `propext`, `Classical.choice`, and `Quot.sound`;
- forbidden-declaration scan is empty.
