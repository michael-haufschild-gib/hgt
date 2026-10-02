# Complete native lcm-sector payment

- **ID:** RP-33
- **Stage:** 3-formalized
- **Route:** RP
- **Status:** Unconditional sector bound proved; RH remains unproved and unfalsified.

## Exact new result

For the actual signed channel A_M(d)=mobiusDivisorDilationChannel M d,
one B>=0 satisfies, for every natural M,

    |sum_{1<=d,e<=M, lcm(d,e)<=M} A_M(d)*A_M(e)| <= B*M^2.

This includes all common-divisor classes and the whole diagonal. It adds
complementary pairs beyond the previously paid d*e<=M sector. An exact
partition leaves every pair with lcm(d,e)>M. No hypothesis concerning
that remaining sector or either native square debt enters the proof.

## Dependency-closed paper proof

Set v_M(d)=V_M(d)/sqrt(M), where V is the actual unsigned clipped channel.
The earlier uniform profile theorem extends to every positive product
d*e<=M: |v_M(d)-c|<=C/e^eta, eta=1/40. Its small-quotient extension uses
the unconditional ceiling |v_M(d)|<=3/5. No endpoint is discarded.

For a complete lcm fibre n and arbitrary f,

    sum_{lcm(d,e)=n} mu(d)*mu(e)*f(d) = mu(n)*f(1).

Finite bilinear lcm Mobius inversion proves this: the divisor-prefix
factor sum_{e|q}mu(e) vanishes unless q=1. Summing n<=M and expanding
around v_M(1) gives exactly

    normalized sector = v_M(1)^2 * sum_{n<=M}mu(n)
      + sum_{lcm(d,e)<=M}mu(d)*mu(e)*
          (v_M(d)-v_M(1))*(v_M(e)-v_M(1)).

Write d=g*a,e=g*b with a,b coprime. Then lcm(d,e)=g*a*b. The two
centered errors are at most 2C/b^eta and 2C/a^eta, respectively.
Only now take absolute values and drop the Mobius and coprimality masks.
The gcd map is injective into all positive triples with g*a*b<=M;
there are floor(M/(a*b)) possible scales. Hence the remainder is at most

    4*C^2*M*(sum_{a>=1} a^(-41/40))^2.

The main term is at most (3/5)^2*M by the elementary Mobius ceiling.
The double p-series converges. Multiplication by M recovers the stated
native quadratic bound. M=0 is handled exactly by the empty sum.

## Lean and audit

- `RHTower.routeP_lcm_pair_sector_quadratic_bound`
  is the unconditional native endpoint in `RoutePLcmPairPayment.lean`.
- `RHTower.routeP_lcm_pair_partition` is the exact unpaid-sector partition.
- `RHTower.routeP_unsigned_profile_product_error` is exposed in
  `RoutePHyperbolicPairDeletion.lean` with a literal public statement.

Both edited leaves passed foreground final `lake --old env lean` audits,
with explicit .olean outputs. New leaf is wired once into RHTower.lean;
no umbrella or full build ran. The new leaf emitted one informational
ring-normalization suggestion, no errors or warnings. Separate /tmp
audit printed the endpoint types and the axiom lists for both new
endpoints, the exposed helper, and the three earlier hyperbolic endpoints:
all use exactly [propext, Classical.choice, Quot.sound]. No added axiom,
placeholder, numerical experiment, resource override, subagent, or commit.

Global lint exited1 on eleven unrelated unreachable modules; neither
edited leaf was flagged. Index refresh exited0 and regenerated the API,
gap, and overview documents. The global lint result is not a pass.

## Remaining hard problem

Prove a uniform quadratic upper bound for the full signed lcm(d,e)>M
sector, or falsify it. Both native RP square debts remain open. Incomplete
lcm packets leave moving truncated divisor sums; the complete-packet
cancellation above cannot be applied beyond its actual domain.
