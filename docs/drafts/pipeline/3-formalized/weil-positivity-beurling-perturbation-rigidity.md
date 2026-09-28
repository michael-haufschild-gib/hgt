# Beurling rigidity of Weil positivity

**Status:** formalized (Lean, unconditional, standard axioms).
**Module:** `formal/GaloisForLFunctions/RHTower/WeilPositivityBeurlingPerturbationRigidity.lean`

## Statement
Fix ζ's archimedean Weil term and pole. Perturb the prime measure `Σ Λ(n)n^{−½}δ_{log n}` by `μ₁ − μ₂`, where `μ_i` are finite measures carried by `[ε, ∞)` and `ε > 0`. If the perturbed symbol `S_Λ(τ) − ∫2cos(τu)d(μ₁−μ₂)` has nonnegative energy on every polar-constrained `C²` test at every level, then `μ₁ = μ₂`. In particular, no prime atom can be moved.

## Proof
Concentration of spread radical tests where the perturbation symbol is positive; prime-blind probes when it is nonpositive; Fourier uniqueness of the symmetrized measures.

## Context
This comes from the Minkowski-problem route (user steer). The polar constraint is Minkowski's closure condition for the normals `(e^{x/2}, e^{−x/2})`. The theorem closes the openness step of Alexandrov's existence scheme at ζ.
