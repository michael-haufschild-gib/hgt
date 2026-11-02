# Exact spline cone cancellation with bounded local density

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** SC2.
- **Statement:** Exact spline coefficients and unit multiplicities admit an
  off-line two-prime cone model with uniformly bounded local atom counts.

For distinct primes `p,q` and `0<d<D`, there is a countable injective core
`z_i=δ_i+iγ_i` with `d≤δ_i<D`, `γ_i≥1`, and real parts cofinal at `D`.
Put `F(z)=(sinh z/z)^8`. Then:

- Every `F(z_i)` is nonzero; `Σ|F(z_i)|≤2`.
- Every real exponential moment converges absolutely.
- Every positive `log p,log q` cone moment is exactly zero.
- Every core unit-height window embeds into `Fin 3`; its truncation at
  `|γ|≤T` embeds into `Fin floor(T)`.
- All sign/conjugation quartet atoms are distinct, with unit multiplicities.
  Every quartet unit-height window embeds into `Fin 12`.
- The even real quartet kernel has mixed natural-cone coupling bounded by `20`.

Thus exact spline weights, integer multiplicities, joint prime-clock separation,
and even a uniform local count do not force RH from bounded cone coupling.
The construction is not a configuration of actual zeta zeros; SC2 remains open.

## Proof

For continuous Hilbert-valued `f`, `|f|≤B`, choose one interior node from
each of `n` unit cells with squared quadrature error at most `nB²`.
Subtracting each cell mean makes the integrated cross term vanish; choose
a point whose squared accumulated error is no greater than its mean.
Apply this simultaneously to spline numerators and both derivative/dual
pairings. Continuous pairings are the identity up to endpoint errors.

The correction `u_y` has displacement at most `1/4` and spatial Lipschitz
constant at most `1/2`. Hence `x↦x+u_y(x)` is strictly increasing; corrected
nodes in one unit interval have cell indices differing by at most two.
A closed-ball inverse theorem realizes arbitrary sufficiently small finite
moment targets while preserving the three-node bound.

If primitive data and frequency count are at most `X≥1`, explicit parameters
give inverse correction radius `O(X³)`, inverse sampling tolerance `O(X⁴)`,
node count `O(X¹⁶)`, and height threshold `O(X²⁰)`. Baker separation and a
fixed shifted-frequency gap make these costs geometric on growing cone windows.

Use levels `δ_k=D−(D−d)2^(−k)`, correction masses `A_k=exp(−4^k)`,
and matched heights `H_k⁸=n_k/A_k`. Since `A_(k+1)=A_k⁴`, eventually
`256n_kA_k³≤1`, hence `H_(k+1)≥2H_k`. A late tail also has
`H_k≥span_k+2`, so successive blocks have gaps greater than one.
Prefix extension fixes all previous blocks and cancels the next finite set
of moments. Absolute convergence gives the exact infinite nullseries.
A unit interval meets at most one block; quartet symmetry multiplies the
count by at most four. The existing quartet identity gives coupling `≤20`.

## Lean

Main theorem: `ConeMoments.exists_two_prime_sparse_prescribed_spline_cone_model`
in `ArithmeticCouplingTheory/ConeMoments/SparseSplineQuartets.lean`.
The exact core theorem is `exists_two_prime_sparse_prescribed_spline_nullseries`
in `SparseSplineNullseries.lean`.

Finite interpolation: `exists_two_prime_sparse_spline_finite_correction`.
Geometric costs: `exists_two_prime_sparse_spline_geometric_corrections`.
Separated schedule: `exists_two_prime_sparse_spline_tail_schedule`.
Compatible prefixes: `exists_sparse_spline_prefix_heights`.
Global count: `unit_interval_embedding_of_separated_blocks`.

All new modules pass direct `lake --old env lean` checks. Main declarations'
transitive axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. The arithmetic-coupling umbrella imports every new module.
External priority has not been checked.
