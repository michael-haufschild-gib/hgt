# Cone cancellation with bounded local density

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** SC2; tests whether local zero counts exclude exact-spline cancellation.
- **Target:** For distinct primes and `0<d<D`, construct the exact-spline
  quartet cone model with uniformly bounded atom count on every unit height interval.

Retain distinct quartet atoms, unit multiplicities, exact coefficients
`F(z)=(sinh z/z)^8`, real parts in `[d,D)` cofinal at `D`, summable
coefficient norms, and vanishing positive two-prime cone moments.
This would exclude a generic SC2 proof from these properties plus the actual
`O(log(2+|T|))` local zero count. It would not settle SC2.

## Proved finite interpolation

For any finite set of positive two-prime cone frequencies and `δ>0`, there
are `n≥1`, `H₀>0`, `κ>0` such that, for every `H≥H₀` and targets
`|r_i|≤κn/H⁸`, distinct heights `γ_j∈[H,H+n+2]` satisfy

`Σ_j F(δ+iγ_j) exp(i t_i γ_j)=r_i`.

Every interval `[T,T+1]` contains at most three heights. All coefficients
are prescribed; multiplicities are one.

**Lean:** `ConeMoments.exists_two_prime_sparse_spline_finite_correction`
in `ConeMoments/SparseSplineInterpolation.lean`. Its finite-data version,
`exists_sparse_prescribed_spline_correction_data`, records explicit costs.
Direct audits use only `propext`, `Classical.choice`, and `Quot.sound`.

### Proof mechanism

For bounded continuous Hilbert-valued `f`, `|f|≤B`, select one interior node
from each unit cell so

`|Σ_j f(x_j)−∫_a^(a+n) f|²≤nB²`.

Subtract each cell mean. The integral of squared accumulated error increases
by its variance, at most `B²`; choose an interior point no worse than this
mean. Apply this simultaneously to spline numerators and the ordinary and
conjugate derivative/dual pairings. Continuous pairings equal the identity
up to uniformly bounded endpoint terms; normalized sampling error is
`O(n^(-1/2))`.

For `m` frequencies, the correction satisfies
`|u_y(v)−u_y(w)|≤2m·inverseSplineBound(δ)·|y|·|v−w|`.
Choose radius `ρ` so displacement is at most `1/4` and this Lipschitz
constant at most `1/2`. Thus `x↦x+u_y(x)` is strictly increasing. Corrected
nodes in one unit interval have cell indices differing by at most two.
The closed-ball inverse theorem realizes the exact targets.

Let `P,Q,I,J,B₀,G` bound displacement, summed second derivatives,
reciprocal numerator, summed Jacobian endpoint errors, numerator, and
summed slopes. Let `η` be the shifted-frequency gap and `M₀=2B₀/η`.
For sampling dimension `q=m+2m²` and coordinate bound `B`, use

`ρ=1/[8(1+P+2mI+QP²)]`, `ε=ρ/[16(m+1)]`, `κ=ρ/4`,

`n=floor(1+((q+1)B/ε)²+16J+16M₀/ρ)+1`,

`H₀=1+64((n+2+δ)G+B₀)P+64(n+2+δ)B₀/ρ`.

These choices give Jacobian error at most `1/4`, baseline at most `ρ/4`,
and the required displacement, monotonicity, and denominator bounds.
Supporting proofs: `StratifiedQuadrature`, `SparseSplineNodes`,
`SparseSplineSampling`, `SplineNodeAverages`, `SparseSplineJacobian`,
`SparseSplineFiniteCorrection`, and `SparseSplineParameters`.

## Infinite construction: remaining claims

If all primitive scalar data and `m` are bounded by `X≥1`, the formulas give
`ρ⁻¹=O(X³)`, `ε⁻¹=O(X⁴)`, `n=O(X¹⁶)`, `H₀=O(X²⁰)`.
`ConeMoments/SparseSplineCosts.lean` proves these bounds and
`exists_sparse_spline_correction_polynomial_bound`; its direct audit has only
standard axioms. `exists_two_prime_sparse_spline_geometric_corrections` in
`ConeMoments/SparseSplineConeCosts.lean` combines these bounds with Baker
separation and the fixed shifted-frequency gap. It gives geometric costs on
cone windows, uniformly on `[d,D]`, with a direct standard-axiom audit.

For `A_k=exp(−4^k)` and matched heights `H_k⁸=n_k/A_k`,
`A_(k+1)=A_k⁴` implies `H_(k+1)≥2H_k` once `256n_kA_k³≤1`.
Geometric node growth makes this eventual. The same late tail can satisfy
`H_k≥span_k+2`, giving `H_k+span_k+1<H_(k+1)`.
A unit interval then meets at most one block. Prefix extension fixes all
old blocks, so their local counts survive the exact nullseries construction.
`eventually_matched_spline_height_double` in
`ConeMoments/SparseSplineBlockSeparation.lean` proves the doubling estimate;
its direct audit uses only standard axioms.
`exists_two_prime_sparse_spline_tail_schedule` in
`ConeMoments/SparseSplineSchedule.lean` supplies the separated schedule with
all local-count and exact-correction properties, also with a standard-axiom
direct audit. `exists_sparse_spline_prefix_heights` in
`ConeMoments/SparseSplinePrefixes.lean` preserves old blocks and their local
counts while cancelling every finite prefix, with the same audit result.
The global count, infinite series, and quartet model remain unformalized.

No bounded-local-density countermodel is claimed yet. The existing model's
global linear height count does not imply a local logarithmic count.
