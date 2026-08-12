# Route E Ramaré Gibbs mean-leakage covariance transfer

- **ID:** `ROUTE-E-RAMARE-GIBBS-MEAN-LEAKAGE-001`
- **Stage:** 3-formalized
- **Type:** `[SHARP CONDITIONAL-MEAN TRANSFER]` / `[ALL-ORDER HISTORY CONSUMER]`
- **Parent:** `route-e-ramare-recombination-ternary-antiscale-law.md`
- **RH used:** no
- **Computation used:** no
- **Literature used:** no; internal-corpus derivation

## Result

For a finite physical cell with nonempty incidence sets `F_x subset P`, positive Gibbs weights
`w_x`, and `|f_x|<=1`, assume

```text
|log(w_x/w_y)| <= eta.
```

With normalized physical coefficients `a_x=w_x f_x/sum_y w_y`, Lean proves

```text
sum_(x,y) C(F_x,F_y) Re(a_x conj(a_y))
  <= (|uniformMean(f)| + 2*tanh(eta/4))^2.
```

Proof uses two exact results: incidence-complement conditional negativity bounds the quadratic
form by `|sum_x a_x|^2`, and pairwise likelihood-ratio oscillation bounds physical-versus-uniform
mean defect by `2*tanh(eta/4)`. No positive centered covariance estimate remains.

For arbitrary-order equal-product histories in `[X-H,X+H]`, Lean instantiates

```text
eta = |R| H^2 / (X (X-H)).
```

This directly realizes physical-vs-uniform conditional mean control on all-order product-history
incidence covariance.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.Sieve.RouteERamareGibbsMeanLeakage
```

Principal declarations:

```text
routeENormalizedWeightedCoefficient
routeE_sum_normalizedWeightedCoefficient
routeE_incidenceComplement_gibbs_le_tanhMeanLeakage
routeE_productHistory_incidenceComplement_le_tanhMeanLeakage
```

Module is imported by `GaloisForLFunctions.RHTower`. Direct `lake env lean` check and targeted
module build pass. Kernel axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, `admit`, new `axiom`, `opaque`, `unsafe`, route premise, or numerical computation
occurs.

## Frontier consequence

Centered Ramaré incidence covariance and Gibbs curvature are no longer independent Route E
obligations. Their composition leaves one explicit scalar: uniform mean on each physical history
cell. For binary component histograms this mean is the known product bias. Open burden is signed
enumeration/cancellation of these uniform cell means under the source-faithful sharp cutoff, then
transport through zero/one-large-prime and moving recurrence seams. Route E and RH remain open.

## Log

- 2026-08-12 — sharp tanh mean-leakage covariance bound and arbitrary-order equal-product-history
  consumer proved in Lean; umbrella import and targeted audit passed.
