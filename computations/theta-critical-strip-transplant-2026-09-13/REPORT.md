# Moving nonreal multiple zeros into the critical strip

All eight numerical continuation tracks reached the two prescribed imaginary heights, using two distinct third-source interventions and two step sizes. Four distinct endpoints passed independent source checks. This is a structural change from the preceding outside-strip examples: the selected zeros now satisfy 0 < Re s < 1 under s = 1/2 + i t.

| Added intervention | Im t | Re t | Uniform multiplier deviation bound |
|---|---:|---:|---:|
| product | 0.125 | 37.904570665422 | 0.051767082453 |
| product | 0.25 | 37.909637504142 | 0.051108237988 |
| square | 0.125 | 38.074162452473 | 0.056935034767 |
| square | 0.25 | 38.066802037106 | 0.056406774280 |

The source is the literal theta cosine kernel multiplied by 1 + alpha h1 + beta h2 + eta h3. The cosine polynomials h1 and h2 have coefficient L1 norm one and separately preserve mass and second moment. For the product intervention, h3 is h1 h2 compensated by constant/cosine terms to preserve both moments. For the square intervention, h3 is h1² with the same two moment corrections, then normalized to coefficient L1 norm one. Exact coefficients and precision-specific source definitions are archived. The displayed bound is |alpha| + |beta| + |eta| times the coefficient L1 norm of h3, guaranteeing a positive multiplier. Theta's original kernel is positive; positivity of the conductor-5 character kernel is not asserted.

The algorithm solves three real equations for the three source amplitudes and then solves the fourth equation for Re t, retaining F=F_t=0 as Im t is decreased. Step sizes 0.08 and 0.04 independently reach corresponding endpoints. The paths are numerical continuation, not a certified global branch genealogy. The 100/160-digit endpoint coordinates and amplitudes agree within 4.13e-97. Nonzero second derivatives distinguish double-zero candidates from a numerically flattened higher-order zero. Independent 190-digit literal-source quadrature yields maximum scaled F/F_t residual 9.61e-155; nearby nonzero anchors agree within 7.84e-158. Scaling by exp(pi t/4) removes ordinary decay and leaves zero locations unchanged. Truncation and quadrature have not been interval-certified.

Consequence: within these explicit source families, positivity of the theta source, reflection symmetry and two unchanged even moments permit numerical nonreal double zeros even inside the RH strip. The product and square interventions show that this result is not tied to one third-source polynomial. This rejects a selector using only those retained properties. It does not perturb an Euler product while preserving it, establish the actual HB source, prove a counterexample for undeformed zeta/L, or supply physical extinction. Positive salvage is an inverse source-design construction with an explicit invariant ledger. The next discriminating question is whether actual arithmetic compatibility blocks such surgery; merely decreasing the perturbation bound would not answer it.

Timing: one guard, 158.478 seconds total, 656.913 recorded worker seconds, 14 workers maximum and native threads one. Original downloads checksum-verified; owned process group cleaned. No Lean builds or changes to other agents' files.
