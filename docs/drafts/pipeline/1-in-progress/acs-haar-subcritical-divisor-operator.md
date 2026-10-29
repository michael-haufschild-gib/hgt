# Transfer the actual Haar divisor reserve to subcritical valuation coordinates

- **ID:** acs-haar-subcritical-divisor-operator
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** ACS: full-source effectivity → Hodge index → RH.
- **Parent:** [signed Haar head payment](acs-low-haar-head-payment.md)
- **Target:** Pay the full signed Haar Gamma/central-mass remainder with
  the original divisor reserve, retaining both poles and every low index.

## Established actual-source transport

Use `x_a=d_a/sqrt(2a+1)` and `w_a=(2a+1)*M_a`. Each original
edge becomes `Lambda(m)*w_b*(x_a/m-x_b)^2`; the absent root
becomes `Lambda(2a+1)*w_a*x_a^2`. The logarithmic lower bound
`log((k+1)/k) >= 2/(2k+1)` gives `w_a >= 1/2`. Thus the exact
source is one half of the unweighted `q=1/p` graph form plus
the nonnegative graph form with weights `w_a-1/2`.

Complete only the finitely many prime coordinates occurring in the
source. For their set Q put `C_Q=sum_(p in Q) log(p)/(p^2-1)`.
The required boundary compensation is
`T_Q(x)=(1/2)*sum_a (C_Q-O_model,X(a))*x_a^2`, where `O_model,X` is
the actual finite inverse-square outgoing row. Then
`D_X + T_Q = (1/2)*sum_e E_Q(e)*|xhat(e)|^2 + R_X`,
where `E_Q(e)=sum_(p in Q,e_p>0) log(p)*(e_p+1/(p^2-1))` and
`R_X` is the exact divisor form with receiving weights `w_b-1/2`.
Both T_Q and R_X are nonnegative. Every finite outgoing row injects
into the convergent prime-power ladders, proving `O_model,X(a)<=C_Q`.
This completion needs no contribution from primes outside Q, since
every nonzero original prime edge already belongs to Q. The transform
uses the complete product Blaschke basis at `q_p=1/p`; the actual finite
source belongs to the original maximal operator domain, and the full
occupation series is summable.

The [actual-source occupation transport](../3-formalized/acs-haar-subcritical-source-transport.md)
has passed its direct Lean check, including the nonnegative boundary cost.
The missing odd root remains a zero coordinate of the actual source;
this does not assert orthogonality to the transformed ground state.

## Remaining joint target

Pay T_Q and the original Gamma/central-mass remainder with the same
divisor reserve. The nonnegative completion cost cannot be dropped
from the upper side of the occupation bound. Retain the full defect
and both original poles; `P>=-7*mass/144` is available independently
of Gamma. The [signed Gamma bound](../3-formalized/acs-haar-gamma-off-diagonal-mass.md)
retains the actual boundary measures, including touching cells.

No joint signed head sign is proved. A scalar improvement or a new
spectral criterion is not the target. The fixed-ratio separated-matrix
theorem supplies no uniform touching limit or payment for this source.
No web search, novelty checks, numerical experiments, or axiom checks.

## Exact Gamma graph; joint comparison remains open

`TheHaarGammaCrossTermsArePositive` now proves the complete summable
positive Laplace expansion of each actual Gamma cross-entry, including
touching pairs. `TheHaarGammaDebtIsAnAdditiveGraph` retains every signed
coefficient in the exact original identity
`W(h)+G_X(u)=D_X+P(h)+sum_a V_X(a)*u_a^2`, where
`u_a=sqrt(2a+1)*d_a`, G_X is a nonnegative additive graph energy and
V_X is the explicit signed diagonal including the original outgoing
charge. These identities have passed Lean; no positivity of V_X or
payment of G_X is claimed. The next target is their combined comparison
with the retained multiplicative divisor form and boundary charge.

`SignedArithmeticEnergyIncidence.FrustrationIsPaidAlongCanonicalPaths`
supplies the exact signed ground-state decomposition and shared-edge
path method. Its `PathCertificate` assumes both a signed supersolution
and the path packing bounds; neither is available for the actual Haar
matrix. A useful application must construct and prove those payments
from the original source. Prime-division paths to the charged absent
root stay inside the horizon and retain the weight `M_b/n_b`; this is
a candidate comparison with the additive Gamma graph, not a certificate.
