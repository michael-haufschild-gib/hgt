# Mass-shifted Gauss bulk and admission-effectivity action (2026-08-13)

## New unconditional Lean results

Modules:
- `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionGaussBulkLowEdgeFloor.lean`
- `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionGaussBulkEffectivityCoercivity.lean`

Both wired into `formal/GaloisForLFunctions/RHTower.lean`.

### Degree-uniform source noncollapse
For any positive moment block and n>=2:
`2 * beta_1 < E_n - (n+1) * beta_(n+1)`.
For normalized shifted-Xi, beta_1(w)->1/8, hence one W gives literal normalized adaptive arithmetic Gauss bulk >1/8 for every degree n>=2 and every actual positive block. False RH implies cofinal strict-frontier right rays with this floor.

### Admission effectivity
Define
`kappa_n = 4n + (n+1)^2/(3n/4+1)`
and
`R_n(y) = -2 firstCoeff_n(y) + (2n+1) alpha_n(y)`.
Then
`N_n'(y) = -R_n(y) N_n(y)`
and
`R_n^2 + 2 kappa_n beta_1 < kappa_n (E_n-(n+1)beta_(n+1))`.

At physical mass y, bulk is literal admission-selected adaptive mixed/completed rational--Gamma-minus-von-Mangoldt P^sharp source minus `2(n+1)N_(n+1)`, divided by `2N_n`. Source equals current source-first shear quotient before observation/reflection.

### Actual integral action
For a<=b, a>1/4, and positive (n+2)-block throughout [a,b], continuity/integrability are automatic and:
`integral_a^b R_n = log N_n(a)-log N_n(b)`
and
`(log N_n(b)-log N_n(a))^2 <= (b-a) kappa_n integral_a^b B_n^arith`.
Uses corpus `HTGeometry.IntegralCauchySchwarz`; no computations.

Principal capstone:
`log_norm_sub_log_norm_sq_le_literalArithmeticGaussBulk_action_of_posDef`.

## Failed conjectures / exact obstruction
- Projective renewal controls wrong-degree edge and arbitrary retained inventory blocks coercive comparison.
- Reciprocal-tail and Hilbert-channel summability are fixed-polynomial; no uniform control for degree-varying adaptive packets.
- Existing two-atom projective theorem explicitly allows summable weighted cascades.
- Uniform normalized bulk does not preclude reciprocal-mass Zeno accumulation at t=1/y -> 0.

Remaining exact open core: all-degree source-preserving admission action with finite total arithmetic budget and nonsummable renewal weights, or nonlinear centered relative action. Fixed-degree action does not compare packets after degree changes.

## Verification
Direct `lake env lean` checks pass. Targeted build of effectivity module passes and builds low-edge dependency. `scripts/formal_tools.py lint` passes. Axiom audit: only propext, Classical.choice, Quot.sound. No stale Lean process.

Report equations 9.3.733--740 in `docs/reports/mass-shifted-spectral-trace-route.md`. Formalized card: `docs/drafts/pipeline/3-formalized/mass-shifted-gauss-bulk-low-edge-floor.md`.

Novelty status: [NOVELTY UNVERIFIED]. arXiv audit found classical Jacobi sum rules, Hankel/Toda norm flow, and varying-weight asymptotics but no route-specific arithmetic source/effectivity law.

Related prior memory: `mem:research/mass_shifted_pole_free_source_charge_flow_2026_08_13`.