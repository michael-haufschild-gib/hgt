# Dropping nodal curvature from almost-everywhere convergence

- **ID:** selberg-nodal-limit-shortcut-28
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement tested:** An almost-everywhere vanishing regularized derivative-energy remainder can be discarded in the compact integral without further control.
- **Scope:** This shortcut fails for the exact local profile h(x)=x. The profile is not a Maass eigenform. The regularized actual-source route remains active.

## Killing mechanism

The actual C² regularized radius r_e(x)=sqrt(x²+e²) satisfies

`r_e''(x) = e²/r_e(x)³ = (1-r_e'(x)²)/r_e(x)`.

The integrand tends to zero away from the single node, hence almost everywhere. Actual FTC gives `integral_{-1}^1 r_e'' = 2/sqrt(1+e²)`, which tends to two. Almost-everywhere convergence by itself does not justify the proposed removal.

## Strongest positive survivor

For every pair of real endpoints, the actual curvature is interval integrable and

`integral_a^b r_e'' = b/r_e(b)-a/r_e(a)`.

Its limit is exactly `b/|b|-a/|a|`, using quotient zero at zero. This classifies the surviving nodal contribution on all oriented intervals, including a half contribution when the node is an endpoint. The survivor is stronger than a negated interchange claim.

## Actual-source salvage

Retaining this mechanism led to a proved standard-area identity for the original Maass congruence trace:

`integral R_e/rho_e = top_e + lambda*integral D/(y²*rho_e)`.

Actual modular symmetry proves every side/arc matching condition, and all integrability is proved. The nonnegative left side is retained; no quarter constant or regulator limit is assumed.

## Status and new insight

Paper proofs are dependency-closed and the exact statements are formalized in `SelbergNodalCurvature` and `SelbergMaassRegularizedArea`. Six relevant targeted builds passed; all 88 audited public declarations use only standard Lean/mathlib axioms or none. Repository lint is separately limited by two unrelated unwired Fokas–Lenells modules. The mathematical insight for the next comparison is that a direction reversal can retain integrated curvature while its pointwise angular residual disappears. Any zero-regulator transport argument must account for that concentration.

[Full paper proof, source mapping, and audit](../3-formalized/selberg-regularized-curvature-and-nodal-charge.md). [Active main goal and next conjecture](../1-in-progress/selberg-quarter-conjecturing-loop.md).
