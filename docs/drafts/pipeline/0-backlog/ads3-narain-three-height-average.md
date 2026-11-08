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

## Mechanism and boundary

Exact scalar projection identifies `F` with the triple angular integral
of `Z_(ρ,σ)(τ)`. Poisson triality exchanges target-area and worldsheet
variables; the mirror-charge involution exchanges the target variables.
The uniform target-horocycle Gaussian majorant must justify all three
integral interchanges. Positivity of the literal scalar heat sum then
gives the lower bound separately in each height.

Corpus search supplies Poisson triality, scalar projection and the
uniform target bound, but not this three-height identity. Mirror symmetry
and joint norm-Fubini remain formalization inputs. This is a lower bound;
it supplies no RH-strength remainder upper bound.

## Gates

- [ ] 0 → 1: prove mirror symmetry and triple angular norm integrability.
- [ ] 1 → 2: exact source symmetry and lower bound proved.
- [ ] 2 → 3: direct Lean checks, axiom audits and umbrella imports.
