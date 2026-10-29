# Transfer the actual Haar divisor reserve to subcritical valuation coordinates

- **ID:** acs-haar-subcritical-divisor-operator
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** ACS: full-source effectivity → Hodge index → RH.
- **Parent:** [signed Haar head payment](acs-low-haar-head-payment.md)
- **Target:** Pay the full signed Haar Gamma/central-mass remainder with
  the original divisor reserve, retaining both poles and every low index.

## Source mechanism under investigation

The checked divisor squares are
`sum Lambda(m)*M_b*(d_a/sqrt(m)−d_b)^2`, with
`n_a*m=n_b`, `n_a=2a+1`, plus the charged absent root.
Investigate `u_a=sqrt(n_a)*d_a`, `pi_a=M_a/n_a`.
The anticipated edge becomes `Lambda(m)*pi_b*(u_a−u_b)^2`.

The comparison measure on odd integers is `1/n^2`. In its unweighted
square-summable coordinates, the prime parameter is `q_p=1/p`.
The corpus provides the complete general-parameter product basis and
maximal-domain operator in `HTGeometry.FiniteBlaschkeNumberOperator`.
The critical `1/sqrt(p)` specialization is not the actual Haar comparison.

The existing mass bounds give the starting comparison
`n/(2n+1) ≤ n*M_((n−1)/2) ≤ n/(2n−1)` for odd `n≥3`.
An exact transport must retain this mass distortion.

## Required work

1. Prove the actual weighted-coordinate identity, including root charge.
2. Complete outgoing edges to the full odd semigroup, prove convergence,
   and retain the identical compensating potential in the original source.
   A finite horizon omits edges to zero coefficients outside it; these
   edges cannot be added without their diagonal compensation.
3. Identify the resulting geometric model with the general-parameter
   number operator, with all basis/domain/summability inputs discharged.
4. Use that structure jointly with the exact Gamma boundary remainders
   to prove the original signed head inequality. A better scalar mass
   constant or a new spectral criterion is not the target.

## Current status

No actual-source spectral transport or joint head sign is proved here.
The [signed Gamma bound](../3-formalized/acs-haar-gamma-off-diagonal-mass.md)
is formalized, retaining the original boundary measures.
The whole divisor-square defect and `P≥−7*mass/144` remain available.
The fixed-ratio separated-matrix theorem supplies no uniform touching
limit and does not discharge this comparison.

No web search, novelty checks, numerical experiments, or axiom checks.

## Exact transport being formalized

Use `x_a=d_a/sqrt(2a+1)` and `w_a=(2a+1)*M_a`. Each original
edge becomes `Lambda(m)*w_b*(x_a/m-x_b)^2`; the absent root
becomes `Lambda(2a+1)*w_a*x_a^2`. The logarithmic lower bound
`log((k+1)/k) >= 2/(2k+1)` gives `w_a >= 1/2`. Thus the exact
source is one half of the unweighted `q=1/p` graph form plus
the nonnegative graph form with weights `w_a-1/2`.

Complete only the finitely many prime coordinates occurring in the
source. For their set Q put `C_Q=sum_(p in Q) log(p)/(p^2-1)`.
The required boundary compensation is
`T_Q(x)=sum_a (C_Q-O_model,X(a))*x_a^2`, where `O_model,X` is
the actual finite inverse-square outgoing row. Then
`D_X + T_Q/2 = A_Q(x)/2 + positive cell-weight remainder`,
and `A_Q` is the completed finite-prime number operator.
This completion needs no contribution from primes outside Q, since
every nonzero original prime edge already belongs to Q. The direct
Lean source transport is in progress; the operator equality and joint
Gamma payment are still unproved.

## Verification checkpoint

- The exact normalized Haar graph decomposition passed a clean direct
  Lean check. Its required olean/ilean now exist and must not be rebuilt.
- Complete paper proof and current formalization list:
  [actual-source occupation transport](../2-fully-proven/acs-haar-subcritical-source-transport.md).
- The scalar Parseval helper is being checked; its first two passes
  exposed coercion normalization errors. No spectral transport is yet
  marked formalized.
- The original missing odd root is explicitly retained as the zero
  valuation coordinate in the source vector.

## Next joint comparison to investigate

The corpus gives the exact positive exponential series
`archLevyDensity(t)=sum_k exp(-(2k+1/2)*t)` for `t>0`
(`RHTower.ArchimedeanAnomaly.archLevyDensity_eq_tsum`). Its four-point mixed difference
on two ordered intervals is nonpositive term by term. Combined with the
actual two-piece balanced Haar profiles, this suggests that their Gamma
off-diagonal matrix entries are nonnegative. This sign is not yet proved
here. A useful next target is a comparison of the resulting additive
graph energy with the retained multiplicative divisor form, including
the ground-state diagonal and the exact boundary charge. A sign theorem
alone would not pay the signed source.

The same module already proves `completelyMonotone_archLevyDensity`,
including nonnegative second derivative. Either its four-point
exponential identity or two integrations against nonnegative Haar
primitives can supply the proposed cross-term sign. These are leads,
not completed Gamma/arithmetic comparisons.
