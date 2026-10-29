# Positive density transfers the exact cutoff gap

- **ID:** ACP-POSITIVE-DENSITY-EXACT-CUTOFF-GAP
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; immediate formalization)
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Lean target:** PositiveDensityTransfersTheExactCutoffGap.lean
- **Input:** ../3-formalized/arithmetic-counting-all-pattern-resolvent-limit.md

## Exact statements

For arbitrary prime pattern P with positive Euler density c, define

Phi_P(s)=-1/s+sum_(m>=2) w_P(m)/(E_m-gamma-s), 0<s<g0=2 log 2.

The exact criterion is

HasGap(omega_P,g) iff g<=g0 and Phi_P(s)<=0 for every 0<s<g.

The exact exhaustion statement is

HasGap(omega_P,g) iff every finite prime cutoff has gap g.

Consequently the finite-cutoff greatest gaps decrease to the actual
greatest gap. This supplies a valid optimal-gap transfer where harmonic
norm approximation alone does not control the unbounded prime form.

Separately, every arbitrary prime pattern, including zero density, has
an attained greatest gap delta_P in [g0*c^2,g0]. Attainment follows
directly from the epsilon definition, not from a zero-density secular
criterion. No cutoff transfer at zero density is asserted.

## Sources read

The corpus search /tmp/acp-infinite-secular-gap-search.json points to
TheFinitePrimeSecularSignsDetermineTheGap.lean and the new all-pattern
mean. The complete finite-prime criterion and supremum source was read,
along with the continuity/root portion of
InteriorSecularRootsForceStrictPrimeGapDecrease.lean. Root continuity is
not required for the proposed exhaustion result.

The private finite weight domination and exact cutoff identity already
proved in InfinitePrimeCountsHaveAZeroOrUnitConductorMass.lean are the
arithmetic inputs. No new monotonicity hypothesis is needed.

## Dependency-closed argument

Positive density makes w_P summable. The first excitation bounds every
positive denominator below by g0-s, so the reciprocal tail is summable.
Splitting off conductor one and using a_P(m)^2=c^2*w_P(m) gives the exact
identity F_P(s)=c^2*Phi_P(s). The ground term -1/s is strictly increasing;
every positive tail term is nondecreasing, so Phi_P is strictly increasing.

At each integer horizon, omega_P equals its finite cutoff F_N. Thus the
existing finite-prime isometry between the twisted harmonic constraint
and the normalized vector's orthogonal complement applies pointwise to
F_N. This uses no fixed-F asymptotic result for a growing F_N. The same
pointwise identification transfers the finite Hermitian reciprocal
criterion. The actual all-pattern ground coordinate tends to c^2>0;
the unique-ground spectral count and ground-energy limit discharge the
criterion's eventual nonzero-coordinate and one-negative-mode conditions.

The full all-pattern resolvent limit now tends to c^2*Phi_P. A positive
limit contradicts any claimed smaller-threshold form bound. Conversely,
if Phi_P is nonpositive below g, strict increase gives a strictly negative
reading at a threshold s between max(0,g-epsilon) and g. The actual
resolvent is then eventually negative and pays the requested form bound.
Nonpositive g follow from the unconditional zero gap. This proves the
exact secular criterion, conditional only on the explicit positive-density
domain.

For the cutoff equivalence, finite-cutoff weights are bounded above by
w_P. Summability therefore gives Phi_(F_Q)<=Phi_P at each physical s.
In the reverse direction, fix a finite conductor packet m=2,...,K+1.
Choose Q>=K+1: all its weights equal those of F_Q exactly. If every cutoff
has gap g, its full nonnegative reciprocal tail is at most 1/s for every
0<s<g. Therefore this packet's tail is at most 1/s. Let K tend to infinity
using summability to obtain the same bound for Phi_P. The criterion gives
the actual infinite-pattern gap. No dominated-convergence interchange is
needed.

For unconditional attainment, the gap set contains zero and is bounded
above by g0. Let delta be its supremum. Given epsilon>0, choose an actual
gap greater than delta-epsilon/2 and apply its definition with epsilon/2.
This proves that delta itself is a gap. The known counted lower bound
then gives delta>=g0*c^2.

The finite-cutoff greatest gaps are antitone by finite inclusion. The
cutoff equivalence makes their infimum an actual infinite-pattern gap and
makes the greatest actual gap a lower bound for all of them. Hence the
infimum equals delta_P, and the antitone convergence theorem gives the
stated limit.

## Audit boundary

Every denominator, finite-horizon sign identification and supremum step
is included in the immediate Lean draft. At zero density, the absolute resolvent
limit is zero and gives no eventual sign; the cutoff equivalence
cannot be extended there by this argument. No complete Weil positivity,
RH conclusion or arbitrary-weight source selection is claimed.

## Immediate formalization

The full nine-endpoint draft is
/tmp/acp-positive-density-exact-cutoff-gap-check.lean. Its endpoints are:

1. Summability of the positive-density secular tail.
2. The exact positive-density normalization F_P=c^2*Phi_P.
3. Strict increase of Phi_P in the physical first gap.
4. The exact positive-density secular criterion for every real gap.
5. Attainment of the greatest gap for every P, without a density condition.
6. The gap set equals the lower interval ending at that greatest gap.
7. The counted lower bound and universal dyadic upper bound on it.
8. The positive-density equivalence with every finite cutoff gap.
9. Convergence of finite-cutoff greatest gaps to the actual greatest gap.

The normalization uses a summable unnormalized series only on the explicit
positive-density domain. It never multiplies a divergent series by zero.
The full actual resolvent leaf passed scratch 37381, its standard-axiom
audit and canonical source check 79210. Its first olean will be needed
for this actual draft. No other new dependency olean is known to be needed.

- [x] Complete paper proof, including unconditional greatest-gap attainment.
- [x] Immediate full Lean draft with matching endpoints.
- [ ] Scratch and transitive axiom audit.
- [ ] Canonical source check, umbrella and durable evidence.
