# Three-height symmetry of the actual Narain average

- **ID:** W11-NA3
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Source:** [Three-modulus symmetry](../1-in-progress/ads3-narain-three-moduli-symmetry.md)

## Conjecture

For `Y,Z,y>0`, put `F(Y,Z,y)=y[1+A_YZ(y)]`, where `A` is the actual
double target-horocycle scalar heat average. Then

`F(Y,Z,y)=F(y,Z,Y)=F(Z,Y,y)`.

Consequently `F(Y,Z,y)` is real and `F(Y,Z,y)≥max(Y,Z,y)`.
Equivalently `A_YZ(y)≥max(Y,Z,y)/y−1`.

The stronger candidate decomposition, with `t=YZy` and
`θ(v)=Σ_(n≥1) exp(−πn²v)`, is

`F(Y,Z,y)=√t+V(t)+2√t[θ(t/Y²)+θ(t/Z²)+θ(t/y²)]`,

where `V(t)=t A_11(t)−2tθ(t)−4√tθ(t)≥0`. After the three explicit
theta terms are removed, the average would depend only on the product
of its heights.

## Mechanism and boundary

Exact scalar projection identifies `F` with the triple angular integral
of `Z_(ρ,σ)(τ)`. Poisson triality exchanges target-area and worldsheet
variables; the mirror-charge involution exchanges the target variables.
The uniform target-horocycle Gaussian majorant must justify all three
integral interchanges. Positivity of the literal scalar heat sum then
gives the lower bound separately in each height.

The [scaling identity](ads3-narain-average-scaling.md) and Jacobi
inversion imply the proposed decomposition. Its positivity follows
from the lower bound by taking `Y→∞`, `Z=y=√(t/Y)`: the elementary
theta contribution is `Y−√t+o(1)`. The
[totient-kernel candidate](ads3-narain-average-totient-kernel.md)
would identify the same invariant as `V(t)=2t Tf(t)`. Neither identity
has yet been formalized.

Corpus search supplies Poisson triality, scalar projection and the
uniform target bound, but not this three-height identity. Mirror symmetry
and joint norm-Fubini remain formalization inputs. This is a lower bound;
it supplies no RH-strength remainder upper bound.

## Gates

- [ ] 0 → 1: prove mirror symmetry and triple angular norm integrability.
- [ ] 1 → 2: exact source symmetry and lower bound proved.
- [ ] 2 → 3: direct Lean checks, axiom audits and umbrella imports.
