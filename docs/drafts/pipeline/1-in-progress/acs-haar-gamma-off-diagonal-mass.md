# Pay the entire signed Haar Gamma cross term in ordinary mass

- **ID:** acs-haar-gamma-off-diagonal-mass
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** ACS: full-source effectivity → Hodge index → RH.
- **Parent:** [signed Haar head payment](acs-low-haar-head-payment.md)
- **Target:** A horizon-independent ordinary-mass bound for
  `Gamma(sum_a d_a H_a)−sum_a d_a² Gamma(H_a)`, retaining all signed
  coefficients and every touching pair, including index one.

## Mathematical mechanism

For disjoint intervals I_i and mean-zero supported profiles f_i, let
`C_ij=integral_(I_i×I_j) f_i(x) f_j(y) K(x,y)` and let A_ij be the
same rectangle integral of `f_i(x)²*(K(x,y)−Far_i(y))`. The corpus
two-interval Gamma inequality, applied to f_i,f_j and f_i,−f_j, gives
`2*abs(C_ij)≤A_ij+A_ji`. Thus both signs of each interaction are paid
by original positive boundary remainders, without a new kernel or a
second Gamma allocation.

Summing the exact cross identity
`Gamma(sum_i f_i)−sum_i Gamma(f_i)=−sum_(i≠j) C_ij`
would give absolute cross cost at most `sum_(i≠j) A_ij`. Disjointness
of the second-coordinate intervals bounds this by the full boundary
remainder of each I_i. The checked remainder-mass estimate is
`integral_(I_i×I_i^c) (K−Far_i)≤exp(1/2)*width(I_i)`.

For f_i=d_i H_i, use `H_i²≤1` and `width(I_i)≤16 M_i`. The target is
therefore `abs(Gamma(h)−sum_i d_i² Gamma(H_i))≤16 exp(1/2)*mass(h)`.
The principal statement should retain the sharper individual boundary
charges before this final scalar bound.

## Proof obligations

- Convert the existing ENNReal two-interval inequality to the signed
  cross pairing, preserving finite-integrability witnesses.
- Prove exact finite assembly of the Gamma cross terms.
- Bound the sum of rectangle remainders by the existing boundary measure.
- Specialize to actual Haar profiles and check the exact Lean modules.

This would control all signed Gamma cross terms in ordinary mass, rather
than their logarithmically weighted diagonal size. It would not by itself
pay the full prime/Gamma head or close ACS. The full divisor-square defect
and both original poles must remain in the subsequent joint comparison.

No web search, novelty checks, numerical experiments, or axiom checks.
