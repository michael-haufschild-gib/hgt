# Prime-only damping filters for a finite exceptional divisor

- **Obstacle:** B13, B134.
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** A finite combination of literal Gaussian prime sums at one height and nearby damping scales recovers any selected top zero's multiplicity, with no continued-zeta or pole term in the observable.

## Proposed identity

Let `s=σ+it`, `y=exp(−at)`, `β=max Re ρ`, and `y_j=y exp(−2jh)`.
Gaussian modes satisfy the exact identity

`K(y_j,ρ−s)=exp(jh(ρ−s)) K(y,ρ−s)`.

For a selected top point `ρ₀`, choose `h>0` sufficiently small and let `P`
vanish at `exp(h(1−β))` and every distinct `exp(h(ρ−β))` in the finite
exceptional divisor except `ρ₀`. Its value at `exp(h(ρ₀−β))` is nonzero.
Set

`A_P(t)=Σj P.coeff(j) exp(−jh(β−s)) Σn Λ(n)n^(−s) exp(−y_j n²)`.

The target is

`A_P(t)/K(y,ρ₀−s) → −mρ₀ P(exp(h(ρ₀−β))) ≠ 0`.

The pole and unwanted finite modes cancel exactly. The uniform complementary
error is `O((y+y^((σ−θ)/2))log t)`, while the unremoved continued logarithmic
derivative is `O(t)`; both vanish against the supercritical target mode.
The filter spacing can be arbitrarily small.

## Significance and open input

This would remove cancellation between top ordinates at the same height and
replace the corrected B134 observable by a literal finite combination of prime
sums. An independent arithmetic upper estimate is still required; the identity
alone does not prove B13.
