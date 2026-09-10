# HB: global growth of the full theta half-square and native circle mean

Status: four source-growth theorems formalized. Complete physical extinction and RH remain unproved.

For every actual Xi occurrence `rho`, let `Q` be the original complete theta-cusp half-square, including both Weyl powers and every signed Fourier mode. Put

```
kappa = 1+2|Re rho-1/2| = 2 max(Re rho,1-Re rho).
```

The new leaf proves `1<=kappa<2` unconditionally. There is a nonnegative constant `C`, depending only on the occurrence, such that on the entire upper half-plane,

```
|Q(x+iy)| <= C max(1,y,1/y)^kappa.
```

For the original radius-`d` circle about `x+i exp(k)`, every source value and its normalized circle mean satisfy

```
|Q(circle(d,theta,x,k))| <= C exp(kappa(d+|k|)),
|mean(Q,d,x,k)|         <= C exp(kappa(d+|k|))           (d>=0).
```

The same constant works for all horizontal positions, angles, base heights and nonnegative radii. These statements concern the actual full source and its native mean; no angular eigenprojection or supplied growth premise enters the proof.

## Proof mechanism

The actual complete tail bound controls the scalar above height one. Both original Weyl powers are bounded by `y^(1/2+|Re(rho-1/2)|)`. Squaring gives the claimed exponent. Actual smoothness controls the compact lower part of the modular cell. Full modular invariance transports this bound to every point: a modular matrix with nonzero lower-left integer entry sends height `y` below `1/y`; the remaining matrices preserve height. The native circle denominator lies between `exp(-d)` and `exp(d)`. Finally, the norm bound for its normalized integral gives the mean estimate.

## Lean statements

Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceCircleGrowth`.
Namespace: `RHTower.D4BMNativeCircle`.

- `sourceGrowthExponent_bounds`: the strict exponent range from the actual Xi strip.
- `fullSquarePotential_global_growth`: the full half-square bound on every modular image.
- `source_global_growth`: the original circle source bound.
- `mean_global_growth`: the complete normalized native circle mean bound.

## Physical consequence and remaining work

The [terminal-decay proof](../1-in-progress/hb-full-source-terminal-decay.md) extends the source estimate analytically to fixed invariant Laplacian powers through the derivative-stable Fourier families. It derives decay `exp(-4(1-beta)V)` for the terminal source coefficients inside the spin-two-transferred reduced bulk on compact radial and angular domains, including the coincident-radius corner. Those derivative and terminal-integral estimates are paper results, not theorems of this leaf.

The source-circle growth also gives a nonempty delay-Laplace overlap `max(kappa,3/2)<Re w<2` for comparing the native kernel with the existing physical Green profile. Identifying the original inverses there, evaluating the limiting source integral with every physical boundary current, and the independent tensor amplitudes remain open.

## Validation

Foreground scratch `lake env lean` passed. Final audit ran only `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceCircleGrowth`, with 3938 existing own-module caches and 11 package caches frozen. It built the new module in 123 seconds and reported three jobs. No old dependency, full or umbrella build ran.

Only the four new public theorems received `#print axioms` checks. Each reports exactly `propext`, `Classical.choice`, and `Quot.sound`. All six installed source/artifact files are byte-identical to the audited files. The umbrella has one new import and was not built.

`scripts/formal_tools.py lint` passed with existing large-file warnings. Module-filtered lexical research returned all nine declarations, including all four public theorems. Owned Lean/Lake processes completed and scratch artifacts were removed.
