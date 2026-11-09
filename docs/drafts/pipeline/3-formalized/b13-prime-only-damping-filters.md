# Prime-only damping filters for a finite exceptional divisor

- **Obstacle:** B13, B134.
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** A finite combination of literal Gaussian prime sums at one height and nearby damping scales recovers any selected top zero's multiplicity, with no continued-zeta or pole term in the observable.

## Identity and proof

Let `s=σ+it`, `y=exp(−at)`, `β=max Re ρ`, and `y_j=y exp(−2jh)`.
Gaussian modes satisfy the exact identity

`K(y_j,ρ−s)=exp(jh(ρ−s)) K(y,ρ−s)`.

For a selected top point `ρ₀`, choose `h>0` sufficiently small and let `P`
vanish at `exp(h(1−β))` and every distinct `exp(h(ρ−β))` in the finite
exceptional divisor except `ρ₀`. Its value at `exp(h(ρ₀−β))` is nonzero.
Set

`A_P(t)=Σj P.coeff(j) exp(−jh(β−s)) Σn Λ(n)n^(−s) exp(−y_j n²)`.

For every `a>0` with `a(β−σ)>π/2`,

`A_P(t)/K(y,ρ₀−s) → −mρ₀ P(exp(h(ρ₀−β))) ≠ 0`.

The pole and unwanted finite modes cancel exactly. The uniform complementary
error is `O((y+y^((σ−θ)/2))log t)`, while the unremoved continued logarithmic
derivative is `O(t)`; both vanish against the supercritical target mode.
The filter spacing can be arbitrarily small. More precisely, for every `L>0`
one can choose `h>0` with `jh<L` for every sample index. The polynomial has
degree at most `|F|+1`; its coefficients are fixed while its explicit weights
depend on height. Since the target mode grows and the quotient limit is nonzero,
`|A_P(t)|→∞` at all large heights.

For completeness, choose `δ=min(σ−θ,1)` and take height above all ordinates
in `F`. Every zero is then at distance at least `δ` from the observation line:
use vertical distance for `F`, horizontal distance for its complement.
The corpus's distance bound gives `|ζ′/ζ(s)|=O(t)`. Its uniform finite-part
bound plus the `4y` continuum-to-pole error gives the full error bound above.
Each sample weight has norm at most one. Finite summation and the reciprocal
mode bound therefore kill both errors after normalization.

## Lean proof

`ExceptionalLayerTheory/DampingFiltersReadTheExceptionalDivisor.lean` proves
`gaussianMode_geometric_damping`, `primeDampingFilter_expansion`,
`primeDampingFilter_reads_selected_zero`, and
`not_asymptoticAbscissaLaw_has_prime_only_divisor_filters`.
The final direct `lake --old env lean` source audit passed. All five printed
transitive axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`.

## Significance and open input

This removes cancellation between top ordinates at the same height and
replaces the corrected B134 observable by a literal finite combination of prime
sums. Existing Gaussian pole filters act on Fourier test profiles; this filter
acts on actual prime sums at one escaping height. Earlier prime-only multiplicity recovery observes at a fixed existing
zero and sends damping to zero; this theorem observes the high zero-free part
of a vertical line. An independent arithmetic upper estimate is still required; the identity
alone does not prove B13.
