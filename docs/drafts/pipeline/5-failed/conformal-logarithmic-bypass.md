# Conformal factors do not bypass normalized logarithmic invariance

- **ID:** conformal-logarithmic-bypass
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `docs/notes.md`, Next-Cycle Conjecture Plan 1.
- **Statement:** Can a conformal polynomial exponential change the centre-normalized logarithmic dilation mean?

## Exact obstruction

For every complex polynomial `Q` and `δ≥0`, the Poisson mean of
`log|exp Q(φ₁(1/2+δ+iτ))|` equals `Re Q(δ/(1+δ))`.
Subtracting the two boundary means and adding the corresponding centre correction gives zero:
`conformal_normalized_log_dilation_eq_zero`.

Proof: translation induces `ψδ(z)=(δ+(1-δ)z)/(1+δ-δz)`, holomorphic on the closed disc.
The harmonic mean-value identity for `Re Q(ψδ)` gives its value at zero. Subtraction cancels
the centre terms exactly.

## No-go closure

- **Strongest positive survivor:** Complete Laguerre factorization of the Abel kernel.
  For every finite real Dirichlet coefficient vector, total squared Laguerre moments equal
  `Σₘ,ₙ wₘwₙ/max(m,n)`, hence its Abel partial-sum squares. Finite projection residuals tend to zero.
- **Further survivor:** Exact Gram pairings for conformal exponentials and Dirichlet modes;
  the actual critical zeta budget has a finite coefficient-energy/residual decomposition.
- **New insight:** Conformal and Abel coordinates preserve the same unweighted energy.
  A quantitative gain for the variational budget must control coupling to the zeta weight.
  `shiftedBudget` translates that weight while retaining the fixed conformal chart.
- **Paper proof:** Dependency-closed; derivative recurrence, coefficient extraction, finite
  Parseval and dominated radial limits are detailed in
  [the formalized card](../3-formalized/conformal-dirichlet-cross-gram.md).
- **Lean:** `conformal_normalized_log_dilation_eq_zero` in `ConformalDirichletGram.lean`;
  survivors are `hasSum_laguerre_abel`, `dirichlet_projection_remainder_tendsto_zero`,
  `hasSum_polyMollifier_dirichlet`, and `budget_conformal_projection_remainder` in
  `GaloisForLFunctions.ArithmeticInnerFunctionTheory`. Kernel checks pass;
  transitive axioms are only `propext`, `Classical.choice`, `Quot.sound`.
