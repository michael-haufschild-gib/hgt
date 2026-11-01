# Actual Gauss–Mayer trace and its fixed-point continuation

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [three approaches, A](../1-in-progress/argon-three-orthogonal-rh-approaches.md).
- **Input:** [actual Fredholm determinant](gauss-mayer-source-fredholm-determinant.md).

For `n≥1`, put `aₙ=(n+√(n²+4))/2`. The actual Cauchy diagonal trace
`t(w)` used in the Fredholm determinant satisfies, for `Re w>0`,

`t(w)=ζ(w)+Σₙ≥1 [aₙ^(−w)/(1+aₙ⁻²)−n^(−w)]`.

The corrected series converges normally on `Re w>−1`. Its sum is
holomorphic there, with the explicit summand bound

`|aₙ^(−w)/(1+aₙ⁻²)−n^(−w)|≤(|w|+1)n^(−Re w−2)`.

Thus the actual first trace continues holomorphically to `Re w>−1`,
away from `w=1`. No trace formula is supplied as an assumption.

## Proof

The positive number `aₙ` satisfies `aₙ²−naₙ=1`, hence
`aₙ=n+aₙ⁻¹` and `n<aₙ≤n+n⁻¹`. The inverse Gauss branch
`φₙ(z)=(n+z)⁻¹` fixes `xₙ=aₙ⁻¹`, with derivative `−aₙ⁻²`.
Every branch maps the closed coefficient disc `|z−1|≤32/25`
into `|z−1|≤1`. The existing Cauchy-residue trace theorem therefore gives

`Σₖ αₖ,R(branchₙ eₖ)=aₙ^(−w)/(1+aₙ⁻²)`,

where `eₖ(z)=(z−1)^k`. Applying the same theorem to the constant map
`φ=0` with weight one gives trace one for `P:f↦f(0)·1`.

The rescaling in the Hilbert factorization cancels on its diagonal:
`Mₖₖ=αₖ,R(L(w)eₖ)`. To exchange the Cauchy diagonal sum with the
regularized branch sum, retain cancellation before taking norms. On
`|u−1|≤1`, the difference of powers gives

`|(u−1)^k−(−1)^k|≤k|u|`.

Combining this with `|φₙ(z)|≤2/n` and the certified principal-power bounds
on the outer disc yields

`‖(branchₙ−n^(−w)P)eₖ‖≤[2kM(w)+(5/2)|w|M(w+1)]n^(−Re w−1)`,

where `M(w)=2^(Re w)exp(π|Im w|)`. Cauchy's functional has norm at most
`R^(−k)`. The polynomial-geometric series in `k` and the positive-exponent
p-series in `n` are summable independently. Absolute double summability
justifies Fubini in the actual operator expansion
`L(w)=ζ(w)P+Σₙ(branchₙ−n^(−w)P)`, proving the displayed trace identity.

For continuation, differentiate `x^(−w)` along the positive-real segment
`[n,aₙ]`. Since `−Re w−1<0` and `aₙ−n≤n⁻¹`,

`|aₙ^(−w)−n^(−w)|≤|w|n^(−Re w−2)`.

The remaining denominator correction has norm at most
`aₙ^(−Re w−2)≤n^(−Re w−2)`. On each compact subset of `Re w>−1`,
take the minimum real part and maximum norm. The resulting p-series
majorizes every summand uniformly. Each summand is entire in `w`,
so normal convergence proves holomorphy of the correction. Adding zeta
gives the claimed continuation and agrees with the original diagonal
trace on `Re w>0`.

## Lean certificate

Module: `RenormalizedIntersectionTheory/GaussMayerFixedPointTrace.lean`.
Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerTrace`.

- `matrix_diagonal`: cancellation of the actual Hilbert rescaling.
- `norm_remainder_monomial`, `summable_norm_remainderDiagonal`: absolute Fubini bound.
- `hasSum_branch_diagonal`: the actual single-branch fixed-point trace.
- `diagonalTrace_eq`: actual regularized fixed-point trace formula.
- `norm_branchTrace_sub_le`: explicit two-power scalar decay.
- `correctedTrace_locallyUniform`, `differentiableOn_traceCorrection`.
- `continuedTrace_eq_diagonalTrace`, `differentiableOn_continuedTrace`.

Direct production source check passed. All seven transitive axiom audits
report only `propext`, `Classical.choice`, and `Quot.sound`.
Umbrella import is wired; no umbrella build was run.

## Scope

The trace is exactly the diagonal used in the source Fredholm determinant,
not an independently defined scalar surrogate. The single-branch residue
formula is reused; the countable regularization, absolute interchange,
and extended scalar convergence are proved here. No literature-novelty
claim is made.

This establishes the first trace. [Countable word traces](gauss-mayer-countable-word-traces.md)
now supply every higher power on `Re w>1`. Primitive geodesic coding, the
Selberg/scattering determinant identity, and exclusion of off-critical
resonances remain open obligations. No RH conclusion follows.
