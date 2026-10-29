# The actual Haar Gamma interaction is a positive Laplace graph

- **ID:** acs-haar-gamma-positive-laplace-graph
- **Stage:** 3-formalized
- **Type:** THEOREM; every claim formalized and directly checked in Lean
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
`K_ab=J_ab/(sqrt(n_a)*sqrt(n_b))`, this becomes

`Gamma(h)=sum_a (Gamma(H_a)/n_a+sum_b K_ab)*u_a^2
          -(1/2)*sum_(a,b) K_ab*(u_a-u_b)^2`.

The graph weights are nonnegative and retain the original touching
interactions. No sign assumption is imposed on d.

The original full Weil form has the exact joint identity

`W(h)+G_X(u)=D_X(d)+P(h)+sum_a V_X(a)*u_a^2`,

where G_X is the displayed additive graph energy, P retains both original
pole moments, and

`V_X(a)=[Gamma(H_a)+(2*gammaHardyPhaseRate(0)-log(n_a))*M_a-O_X(a)]/n_a
          +sum_b K_ab`.

Here D_X and O_X are the original logarithmic divisor defect and outgoing
charge. The signed potential V_X is retained without a positivity claim.

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
   is integrable. It is the sum of the absolute exponential integrands;
   dominated convergence justifies the full integral-series exchange.
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
5. In the original identity `W=Gamma+2*phase(0)*mass-prime+P`, use the
   exact Haar square mass and
   `D_X=sum_a[log(n_a)*M_a+O_X(a)]*d_a^2-prime`.
   Substitute the Gamma graph identity and `d_a^2=u_a^2/n_a`.
   Collecting the finite diagonal sums gives the full-Weil identity.

## Route status

This identifies the adverse signed Gamma term as an actual nonnegative
additive graph energy and retains the exact signed Weil potential.
It does not show that the combined right side pays the graph energy.
If the valuation representation is used, its completion cost must also
remain. The joint graph payment card stays in progress. No web search,
novelty check, numerical experiment or axiom check is used.

## Exact Lean correspondence

Namespace: `GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells`.
All three modules belong to `ArithmeticCastelnuovoSeveri/`.

| Claim | Module | Declaration |
|---|---|---|
| Increasing-weight moment sign | `HaarLaplaceMoments` | `haarProfile_moment_nonpos_of_monotone` |
| Both exponential moment signs | `HaarLaplaceMoments` | `haarLaplaceLeft_nonneg`, `haarLaplaceRight_nonneg` |
| Exponential integrability and original cell restriction | `HaarLaplaceMoments` | `integrable_haarProfile_mul_exp`, `setIntegral_haarProfile_mul_eq` |
| Actual symmetry and zero diagonal | `TheHaarGammaCrossTermsArePositive` | `haarGammaCoupling_symm`, `haarGammaCoupling_self` |
| Full summable positive expansion, including touching | `TheHaarGammaCrossTermsArePositive` | `haarGammaCoupling_hasSum`, `haarGammaCoupling_nonneg` |
| Exact signed Gamma matrix | `TheHaarGammaDebtIsAnAdditiveGraph` | `haarSectionProfile_gamma_eq_matrix` |
| Symmetric nonnegative graph weights and energy | `TheHaarGammaDebtIsAnAdditiveGraph` | `haarGammaGraphWeight_symm`, `haarGammaGraphWeight_nonneg`, `haarGammaGraphEnergy_nonneg` |
| Exact Gamma row potential minus graph | `TheHaarGammaDebtIsAnAdditiveGraph` | `haarSectionProfile_gamma_eq_row_sub_graph` |
| Full original Weil identity | `TheHaarGammaDebtIsAnAdditiveGraph` | `haarSectionProfile_roughWeil_add_graph_eq` |

## Final validation

All three exact-file commands passed with exit code zero and no warnings,
run sequentially from `formal/`:

```text
lake --old env lean GaloisForLFunctions/ArithmeticCastelnuovoSeveri/HaarLaplaceMoments.lean
lake --old env lean GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHaarGammaCrossTermsArePositive.lean
lake --old env lean GaloisForLFunctions/ArithmeticCastelnuovoSeveri/TheHaarGammaDebtIsAnAdditiveGraph.lean
```

Required dependency oleans were built only for the first two modules;
the graph leaf has no olean. Existing oleans were not rebuilt. All three
imports are wired into the ACS umbrella; the umbrella was not compiled.
Axiom checks were skipped as requested. No paper-only claim remains on this card.
