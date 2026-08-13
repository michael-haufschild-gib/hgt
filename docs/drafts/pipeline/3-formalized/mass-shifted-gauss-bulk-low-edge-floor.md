# Mass-shifted Gauss-bulk low-edge floor and effectivity action

- **ID:** mass-shifted-gauss-bulk-low-edge-floor
- **Stage:** 3-formalized
- **Route:** mass-shifted spectral face, §9.3 exact open core
- **Target:** degree-uniform source noncollapse and admission-effectivity action before reflection

## Proven source law

Let `E_n` be adaptive Jacobi energy and `beta_j` current normalized Christoffel edges. Remove
only source's exact Gaussian-invisible newborn coordinate:

`B_n = E_n - (n+1) beta_(n+1)`.

For every positive block and `n >= 2`:

`B_n > 2 beta_1`.

Because shifted-Xi normalized `beta_1(w) -> 1/8`, one mass threshold implies
`B_n(w) > 1/8` simultaneously for every degree and every actual positive block.

Remaining multiplicative loss is exact admission-effectivity rate

`R_n = -2 a_n + (2n+1) alpha_n = -(log N_n)'`.

With `kappa_n = 4n + (n+1)^2 / (3n/4+1)`, weighted Cauchy proves

`R_n^2 + 2 kappa_n beta_1 < kappa_n B_n`.

At physical mass this `B_n` is literal adaptive mixed/completed rational--Gamma-minus-von
Mangoldt `P^sharp` source minus exact newborn norm, divided by current admitted norm. Across every
positive chamber `[a,b] subset (1/4,infinity)`:

`(log N_n(b)-log N_n(a))^2 <= (b-a) kappa_n integral_a^b B_n(y) dy`.

Continuity and integrability are discharged from block positivity in Lean.

## Significance

Source is formed after adaptive admission and before Gaussian/reflection aggregation. No
orientation map or fixed linear report occurs. Normalized producer cannot collapse along cofinal
degree escape, and literal source pays squared multiplicative admission motion.

## Formal status

- `XiShiftedCanonicalAdmissionGaussBulkLowEdgeFloor.lean`: literal quotient, generic low-edge
  floor, uniform shifted-Xi floor, strict-frontier right-ray noncollapse, false-RH cofinal dichotomy.
- `XiShiftedCanonicalAdmissionGaussBulkEffectivityCoercivity.lean`: sharp pointwise effectivity
  coercivity, literal source/shear mass law, automatic continuity, exact log transport, integral
  source-action bound.
- Both modules wired into `RHTower.lean`.
- Direct `lake env lean` checks pass. Targeted build of effectivity capstone (including low-edge
  dependency) passes. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
  Formal lint passes.

## Failed stronger conjectures

- Projective renewal controls wrong degree and cannot absorb arbitrary retained inventory.
- Fixed-polynomial reciprocal-tail/Hilbert summability gives no uniform control of moving adaptive
  packets.
- Degree-uniform normalized source floor does not exclude reciprocal-mass Zeno accumulation.

## Exact open core

One all-degree source-preserving admission action with finite total arithmetic budget and
non-summable renewal weights, or a nonlinear centered relative action. Fixed-degree action does not
compare packets after degree changes.

## Novelty

`[NOVELTY UNVERIFIED]`. Broad arXiv audit found classical Jacobi sum rules, Hankel/Toda norm flow,
and varying-weight asymptotics, but no shifted-Xi admission-selected rational--Gamma-minus-von
Mangoldt source/effectivity law.
