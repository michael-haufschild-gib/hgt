# The actual Haar Gamma interaction is a positive Laplace graph

- **ID:** acs-haar-gamma-positive-laplace-graph
- **Stage:** 2-fully-proven; direct Lean formalization in progress
- **Type:** THEOREM (paper), `[PROVED HERE]`
- **Route:** ACS: full-source effectivity → Hodge index → RH.
- **Parent:** [joint signed graph payment](../1-in-progress/acs-haar-gamma-signed-graph-payment.md)

## Exact statement

For the actual balanced cells H_a, a>=1, define

`U_a(r)=-integral H_a(x)*exp(r*x) dx`,
`V_a(r)= integral H_a(x)*exp(-r*x) dx`.

Both are nonnegative for r>=0. At rates `r_k=2k+1/2`, every a<b has

`J_ab=-integral H_a(x)*H_b(y)*archLevyDensity(y-x) dx dy
     =sum_k U_a(r_k)*V_b(r_k)>=0`,

with integration over the two original cells. The series is summable,
including when the cells touch. Set J_ba=J_ab and J_aa=0; these agree
with the actual rectangle pairings in both orders.

Every finite signed section has exactly

`Gamma(sum_a d_a H_a)=sum_a Gamma(H_a)*d_a^2+sum_(a,b) J_ab*d_a*d_b`.

For `n_a=2a+1`, `u_a=sqrt(n_a)*d_a` and
`K_ab=J_ab/sqrt(n_a*n_b)`, this becomes

`Gamma(h)=sum_a (Gamma(H_a)/n_a+sum_b K_ab)*u_a^2
          -(1/2)*sum_(a,b) K_ab*(u_a-u_b)^2`.

The graph weights are nonnegative and retain the original touching
interactions. No sign assumption is imposed on d.

## Dependency-closed paper proof

1. H_a is nonnegative to the left of its internal boundary and
   nonpositive to the right, with integral zero. For every continuous
   increasing w, subtracting w at that boundary shows
   `integral H_a*w<=0`. Apply this to exp(r*x), and to -exp(-r*x),
   proving both Laplace-moment signs. Compact support gives integrability.
2. On two ordered cells, y>x almost everywhere. The checked original
   kernel expansion is `k(y-x)=sum_k exp(-r_k*(y-x))`.
   The actual rectangle measure is finite even when the cells touch.
   Since the Haar profiles are bounded, `abs(H_a(x)*H_b(y))*k(y-x)`
   is integrable. Tonelli identifies it with the sum of the absolute
   exponential integrands, justifying the full integral-series exchange.
3. Each exponential separates into exp(r_k*x)exp(-r_k*y). Fubini gives
   its integral as `-U_a(r_k)*V_b(r_k)`. Thus the negative rectangle
   pairing has the displayed summable nonnegative series. Symmetry of
   the original kernel gives the reversed order; a rectangle does not
   cross its own interior, giving the zero diagonal.
4. Apply the checked exact finite Gamma expansion. Scaling each profile
   pulls d_a*d_b out of its rectangle pairing, yielding the stated
   finite quadratic form. Substitute d_a=u_a/sqrt(n_a). Symmetry of K
   turns the expansion of the difference squares into the row potential
   minus the graph energy exactly.

## Route status

This identifies the adverse signed Gamma term as an actual nonnegative
additive graph energy. It does not pay that energy, its row potential,
the central mass or the valuation completion cost. The joint graph
payment card remains in progress. No web search, novelty check,
numerical experiment or axiom check is used.
