# Euler-ray rank-two theta/Weil contraction

Status: Lean-formalized, unconditional cross-route theorem. `[CORPUS-NEW SYNTHESIS]`. Does not
prove RH.

## Exact weld

For `x,y > 1/2`, Lean proves that the RH-critical logarithmic-derivative kernel restricted to
positive real nodes is not a new object:

```text
criticalLogDerivKernel(x,y) = xiSquaredEulerFullKernel(x,y).
```

The right side is the complete multiplicity-exact Xi divisor response already known to have
strictly positive diagonal and strictly positive two-node determinant for `1/2 < x < y`, without
assuming any zero-location statement. Completing squares therefore gives, for every complex
coefficient pair `c`,

```text
Re kernelEnergy(twoChannelKernel,c,[x,y]) >= 0.
```

Transport through the exact Weil parity split and theta/CLG observability weld yields both

```text
O(A_c) + O(B_c) <= E(A_c) + E(B_c)
```

for the canonical linked two-channel packet on `[x,y]`, and nonnegative literal
`thetaCuspTiltSource` tilt flux for every complex two-mode coefficient packet at these nodes.

## New boundary

The prior rank-one result ruled out diagonal failure. This theorem rules out all two-node failure
on the positive Euler ray, including arbitrary complex coefficient interference and the complete
off-critical Xi divisor. Hence an RH-detecting negative packet must use at least one of:

- genuinely non-real node geometry; or
- at least three distinct positive-real Euler modes.

This separates two possible next producers. A real-ray route must attack a three-node determinant
or higher. A two-node route must quantify the complex vertical-phase correction absent from the
squared-Euler chamber law.

## Lean source

`formal/GaloisForLFunctions/RHTower/ThetaCuspTiltFluxWeilParityEulerRayWeld.lean`

Closed declarations:

```text
logDeriv_xiCent_ofReal_eq_fullQ
criticalLogDerivKernel_ofReal_eq_fullKernel
twoMode_twoChannelKernel_realRay_energy_nonneg
twoMode_twoChannelParityEnergy_domination_realRay
thetaCuspTiltSource_twoMode_realRay_tiltFlux_nonneg
```

Verification:

- direct source check passed with `lake env lean`;
- exact target build passed with
  `lake build GaloisForLFunctions.RHTower.ThetaCuspTiltFluxWeilParityEulerRayWeld`;
- no umbrella/full build was run;
- all five `#print axioms` reports contain only `propext`, `Classical.choice`, and `Quot.sound`;
- forbidden-token scan and targeted `git diff --check` passed;
- module is wired into `RHTower.lean`.

## Log

- 2026-08-21 — Identified complete squared-Euler response with critical kernel on the exterior
  positive ray; transported strict two-node determinant through linked Weil parity and literal
  theta tilt flux.
