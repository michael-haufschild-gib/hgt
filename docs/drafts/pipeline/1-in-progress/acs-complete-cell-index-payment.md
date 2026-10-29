# Signed index payment on complete logarithmic cells

- **ID:** acs-complete-cell-index-payment
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** ACS: full-source sections → Riemann–Roch and ampleness → Hodge index → RH.
- **Statement:** The original full arithmetic form `finiteCellWeil` is nonnegative on every finite real complete-cell coefficient vector, with the Gamma, prime, and both pole contributions retained.

## Target

Prove the signed index estimate on the source-complete cells constructed in `CompleteWeilSourceTransfer.lean`. Their approximation of arbitrary finite compact C² source families is formalized. Positivity of separated narrow sections does not settle this estimate.

## Constraints

- Derive every analytic input from the actual arithmetic source.
- No form-defined effectivity hypothesis or assumed positive residual.
- Preserve all successor cells, full Gamma jump energy, and both poles.
- Any proved intermediate mathematical statement must be formalized immediately; no stage-2 parking.

## Current evidence

- `exists_completeFiniteSourceTransfer` recovers the original Weil intersections and polarized Gram entries on one common complete-cell system.
- `finiteCellWeil_original_surface_limit` realizes `finiteCellWeil c 0 1 X` by compact C² tests on the original surface. The same smoothing preserves both pole coordinates and exact Hecke subdivision; its first `X` cell sections are linearly independent at every scale.
- Independent separated-section positivity has a support restriction; complete cells fill the gaps.
- [Balanced complete-cell effectivity](../3-formalized/acs-complete-cell-haar-effectivity.md) is formalized and audited. `exists_haarTail_roughWeil_floor` gives one fixed lower index and a unit-mass floor for all finite signed balanced tails, independently of the upper horizon. `exists_smooth_haar_effectivity` gives, for every dimension, one common smoothing scale with exact dimension, a half-mass floor, Riemann–Roch, ampleness, and Hodge index on the source-defined range. The prime, Gamma, and pole estimates retain all original terms. This proper subspace does not settle the pair averages, low-index directions, or their full mixed coupling.
- [Complete-cell prime triangularity](../3-formalized/acs-complete-cell-prime-triangularity.md) retains both original coefficients on each pair and proves the entire real average-to-detail prime block vanishes. The opposite orientation remains.
- [Gamma payment with arbitrary means](../3-formalized/acs-gamma-payment-with-arbitrary-means.md) removes all local mean-zero restrictions from coherent logarithmic variance payment. `cellPairSum_levyEnergy_ge` pays `Σ log(a)*haarMass(a)*(u_a-v_a)²` in the actual Lévy energy for arbitrary signed coefficients on both cells of every pair. Thus pair averages cannot erase this Gamma detail charge. Their remaining arithmetic and pole coupling is tracked in [mixed payment](acs-complete-cell-mixed-payment.md).
- [Simultaneous Gamma payment](../3-formalized/acs-gamma-detail-mean-boundary-payment.md) retains logarithmic local variance, a positive graph on actual interval means, and exterior mean displacement in the same original Lévy energy. Its compact-BV finiteness and all analytic inputs are discharged in Lean.
- [Coarse Gamma recovery](../3-formalized/acs-coarse-gamma-recovery.md) is formalized with uniform actual row bounds and finite exterior charges. The original full Gamma energy simultaneously pays the entire coarse Gamma energy and logarithmic detail mass, up to one explicit universal constant times actual coarse square mass, for arbitrary original cell coefficients and every finite horizon.
- [Joint non-first-prime payment](../3-formalized/acs-joint-nonfirst-mixed-payment.md)
  includes the full Haar Weil diagonal, Gamma coupling, and every mixed
  exponent at least two, retaining any coarse Gamma share below one and
  positive logarithmic detail energy beyond one fixed head. Its negative
  dimension is uniformly bounded. First-prime mixing and the coarse signed
  block remain outside this payment.
- [Full-pole payment](../3-formalized/acs-full-polar-nonfirst-payment.md)
  restores the actual complete-profile polar term, retaining coarse Gamma,
  positive weighted detail energy and the cosh square. One fixed detail
  head and the actual sinh moment give uniform negative dimension at most
  A+1 for this subform. Removing those index costs and paying the remaining
  first-prime/coarse block are still open.
- [Joint whole-square payment](../3-formalized/acs-joint-whole-square-polar-payment.md)
  spends retained coarse Gamma on the missing coarse square source. The
  enlarged source includes every even prime exponent exactly once, together
  with the full Haar diagonal, all nonfirst mixed powers and the full pole.
  Positive coarse/detail reserves remain. One fixed head and the actual
  sinh and ordinary-mean moments give uniform negative dimension at most
  A+2. Coarse first-prime and odd higher sources, coarse archimedean mass,
  first-prime mixing and these finite index costs remain unpaid.
- Full-source effectivity and the signed Gamma–prime–pole index bound remain unproved.
- [Full Haar prime finite heads](../3-formalized/acs-full-haar-prime-source-finite-heads.md)
  approximate the entire Haar prime diagonal, including first powers, in
  the original complete-profile Gamma norm uniformly in horizon. For the
  full-pole nonfirst mixed source R, one fixed detail head then gives
  `|R−(Γ(F)+P(F))|≤εΓ(F)`, retaining any complete Gamma share below one
  and the exact cosh square. First-prime mixing, coarse signed terms and
  finite head/moment index costs remain open.
- [Uniform prime–polar cancellation in Gamma norm](../3-formalized/acs-prime-polar-cancellation-in-gamma-norm.md)
  proves `|primeSum(f)−P(f)|≤ε exp(R)(Γ(f)+∫f²)` for every BV profile
  supported in [−R,R], with one sufficiently large R threshold for all profiles.
  Every prime power and both pole moments remain. Complete cells now admit
  relative cancellation in their native Gamma-plus-mass norm, without a
  derivative bound. The remaining exp(R) factor does not pay the uniform
  signed index target.

## Log

- 2026-10-28 — Opened after formalizing full finite-source transfer. Investigating actual signed payment; no new sign claim is certified.

- 2026-10-28 — [Smooth complete-cell realization](../3-formalized/acs-smooth-hecke-complete-sections.md) is formalized and audited. Exact source realization and arithmetic compatibility are available; full signed index payment remains open.
