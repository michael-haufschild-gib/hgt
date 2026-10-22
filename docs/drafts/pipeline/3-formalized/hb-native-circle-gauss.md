# HB: native circle equals the physical Gauss kernel

Status: two public theorems formalized and audited. Complete causal-response identification, physical-current extinction and RH remain unproved.

For every complex exponent `alpha` and every real radius parameter `d`, the original height-power circle integral satisfies

```
average_theta (cosh(d)-sinh(d)cos(theta))^(-alpha)
  = legendreKernel(-alpha,cosh(d)).
```

The right side is the existing physical kernel defined by its Gauss series. The theorem proves exact equality, including its normalization at `d=0`, with no branch or convergence premise supplied. Negative radii and terminating parameters are covered too.

For the original complete theta half-square, the second theorem inserts this physical kernel into all three original cusp channels, with their completed amplitudes, and retains the entire signed Fourier remainder. No angular projection is introduced.

## Proof

Set `r=sinh(d)/(cosh(d)+1)` and `a=(cosh(d)+1)/2`. Lean proves `|r|<1` and the exact factorization

```
cosh(d)-sinh(d)cos(theta)
  = a (1-r exp(i theta))(1-r exp(-i theta)).
```

The two complex factors have positive real part and are conjugate to each other. Their principal logarithms add without a branch correction. The corpus's complex binomial theorem gives both series. Absolute norm summability justifies their product and integration. Opposite angular phases integrate to zero unless their indices agree. Lean then identifies the squared diagonal coefficients with the actual Gauss coefficients. These are complex squares, retaining the full exponent dependence.

## Lean statements

Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeCircleGauss`.
Namespace: `RHTower.D4BMNativeCircle`.

- `powerCircle_eq_legendre`: exact native height-power/physical-kernel equality.
- `mean_cusp_expansion_legendre`: full-source expansion through all three actual physical kernels and the complete remainder.

The [comparison card](../1-in-progress/hb-native-cusp-inverse-identification.md) gives the next analytical consequences: `|K_alpha(h)|<=exp(|Re alpha|h)`, the spatial operator bound `h exp(|Re alpha|h)`, and admission of the native principal-response Laplace integral for `Re w>kappa`, where `kappa<2`. Those bounds and identification with the existing Volterra evolution are not yet formalized. The remaining evolution proof must establish the native causal integral's weak equation and operator-domain admission before invoking uniqueness.

## Validation

Foreground scratch `lake env lean` passed. Final audit ran only `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeCircleGauss`, using 3947 frozen own-module caches and 11 package caches. The new leaf built in 99 seconds; Lake reported three jobs. No old dependency, full or umbrella build ran.

Only the two new public theorems received `#print axioms` checks. Each reports exactly `propext`, `Classical.choice`, and `Quot.sound`. All six installed source/artifact files match the audited files byte for byte. The umbrella contains one new import and was not built.

Formal lint passed with existing large-file warnings. Module-filtered lexical research returned both new public theorems. Frontier map and universal ledger were not edited. No mathematical computation ran.

All owned Lean/Lake processes completed. Scratch files and the frozen audit tree were removed.
