# Theta modular orbit discrimination

- **Status:** exploratory source-dynamics attack; no sign theorem claimed.
- **Full chain:** actual theta modular ODE -> native eighth-order reflected D1 sign ->
  theta-specific cofinal/all-order incidence -> full zero exclusion -> RH in Lean.
- **Open cores:** D1 on 0<x<137/2000 and the separate all-order propagation. Closing D1 alone
  would not be an RH proof.

The static chamber permits negative D1 at an unphysical seam scale R=5/2. The actual squared
seam scale is above191/10, where D1 has an unconditional positive polynomial certificate.
The actual three-state source flow is

`S'=3-S²/3-3A/4`, `A'=-2AW`, `W'=2+A/2+2S²/9-2SW/3`,

starting at `(S,A,W)=(0,R0²,0)`. Its mass-normalized theta jets are obtained by the covariant
Lie derivative `L-S/6`; source jet n is `(H_(n+2)-H_n/4)/2`.

Experiment asks whether dynamic incidence supplies a robust compact D1 region, and whether
nearby initial scales separate into distinct long-time behaviors. No numerical trajectory is
substituted for the literal source. The arithmetic initial value is computed from the entire
theta series for guidance, with a finite numerical tail acknowledged.

[Protocol](../2-fully-proven/computations/theta-modular-orbit-discrimination-2026-09-06/PROTOCOL.md).

## B1: current exact algebraic candidate

The box test has no numerical failure. A subsequent exact rational Bernstein conversion finds
all3900 coefficients strictly positive for P on `-1<=S<=0,17<=A<=20,0<=W<=6/5`.
Polynomial multidegree is(24,12,11), with540 original monomials. This is a candidate algebraic
proof, not yet Lean-checked. No D1 closure claim is made until identity, positivity, actual
source admission, and source-factorization are all formal.

Paper admission route from existing source theorems: A<=20 on x>=0, S<=0, W>=0, and seam
A(0)>19.1. Differential fencing gives `-S<=13x` and `W<=14x` for0<=x<=137/2000; the boundary
derivatives lie strictly below13 and14. Then `(A+300x²+x)' >0`, so
`A>=A(0)-300x²-x>17` on the same interval. This places the actual trajectory in B1's box.
This would close the compact D1 gap if the polynomial certificate is verified. All-order
incidence remains a separate unsolved RH producer even after that closure.

The exact source admission theorem is checked in scratch and by the named-leaf audit of
`GaloisForLFunctions.RHTower.ThetaCuspModularCompactTube` (only this leaf compiled).
The remaining formal work is the explicit jet expansion, the positive algebraic identities,
and their transfer back to raw and native D1. Candidate coefficients are not imported as
numerical premises.
