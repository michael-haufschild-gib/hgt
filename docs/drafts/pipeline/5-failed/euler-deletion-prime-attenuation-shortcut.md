# Zero-preserving prime attenuation does not preserve literal deletion admission

**Stage:** 5-failed. **Scope:** the one-prime attenuation shortcut; not all source deformations.
**RH implication:** none. **Novelty:** not certified.

The attempted inference was that a finite Euler-factor quotient preserving zeta's zero
divisor also preserves the ordinary, conditionally convergent deletion source. For coefficients
`b(n)=c^(v_p(n))`, `0<c<1`, the far-right series has continuation
`zeta(s)*(1-p^(-s))/(1-c*p^(-s))`; the quotient is regular and nonzero on `Re(s)>0`.
The elementary geometric-series proof is in the paper card. This zero-divisor comparison
does not establish ordinary convergence of a modified deletion series.

**Exact killing theorem:** keeping the literal coefficient `1-p[p|n]` gives harmonic sums
at least `(1-c)*(1-1/p)*H_N`, hence divergence at exponent one. The ordinary Dirichlet
convergence theorem then excludes convergence at every complex exponent with `Re(s)<1`.
This is Lean-closed as `literal_not_convergent_of_re_lt_one`.

**Strongest positive survivor:** the valuation coefficients have the exact bounded digit
remainder `R(N)=(p-c)S(N)-(p-1)N`, satisfying
`R(N)=c*R(floor(N/p))+(1-c)*(N mod p)` and `0<=R(N)<=p-1`. A deletion multiplier
`ell` has bounded coefficient prefixes exactly when `ell*c=p`. At that unique
normalization, the prefix equals `N mod p-R(floor(N/p))`, is bounded by `p-1`, and its
ordinary Dirichlet series converges throughout `Re(s)>0`.

**New insight:** the repair is explicit and changes the deletion operation. It therefore
cannot be inserted into the original curvature argument while retaining its old coefficients.
The same positive contractive multiplicative weights can support a repaired series and fail
the literal one on the entire open strip.

**Status:** the recurrence, exact normalization classification, harmonic drift, failed
literal admission, and repaired convergence have dependency-closed paper proofs and Lean
proofs in `EulerDeletionPrimeAttenuation`. The Euler-quotient explanation is paper-proved
and is not an exported Lean theorem in that module.
[Paper](../2-fully-proven/euler-deletion-prime-attenuation-admission.md),
[Lean certificate and validation boundary](../3-formalized/euler-deletion-prime-attenuation-admission.md).

The subsequent [compatible-coefficient audit](euler-deletion-compatible-attenuation-repair.md)
also closes the attempt to remove the curvature by this repair: the normalized `2,3,5`
curvature is exactly unchanged for every positive attenuation at five. Its stronger general
factorization and sign boundary are separately paper-proved and Lean-closed.
