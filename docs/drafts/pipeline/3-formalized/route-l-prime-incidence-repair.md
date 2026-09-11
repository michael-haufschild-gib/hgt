# Route L: prime-incidence control and the Green repair obstruction

Date: 2026-09-11.
Status: formalized and audited; 18 unconditional theorems. RH remains unproved.
Module: `GaloisForLFunctions.RHTower.DeningerGibbsPrimeIncidenceRepair`.

## Exact question and outcome

Keep the actual ordinary-integer Gibbs reader and its convergence domain
`D_sigma`, with `sigma>1/2`. For an admitted operator `T`, require cyclicity
only of prime Wold pairs:

`Reader_sigma(S_p^* T S_p) = Reader_sigma(T P_p)` for every prime `p`.

There is no such `T` whose diagonal difference from the literal reciprocal
Green source `Q` is a summable complex family. This includes arbitrary
signed and complex corrections. It imposes no positivity, self-adjointness,
finite support, or composite-dilation cyclicity.

C18's unit-diagonal classification used every integer dilation. The present
prime-only obstruction has a different proof: a uniform arithmetic
incidence bound and divergence of the sum of reciprocal primes. It does
not claim that prime tests alone reconstruct every diagonal coefficient.

## Positive survivor and sharp threshold

For real `a`, prime `p`, and positive integer `k`, put

`K_a(p,k) = 1_(p divides k) * (k/p)^(-a)`.

For `a>0`, every finite prime set `P` and every positive integer `k` obey

`sum_(p in P) K_a(p,k) <= C_a`,

where the finite budget is

`C_a = sum_(j>=0) (j+1)*(2^(-a))^j`.

Consequently every absolutely summable complex family `r(k)` has an
absolutely summable prime-incidence readout

`p -> sum_k K_a(p,k)*r(k)`.

The uniform column-bound threshold is exact: such a constant exists if
and only if `a>0`. At `a<=0`, an integer divisible by every member of a
finite prime set contributes at least one to every corresponding entry.
Arbitrarily large finite prime sets therefore defeat every constant.
In the actual Gibbs parameters, `a=2*sigma-1`; the failure occurs precisely
at and beyond the neutral endpoint excluded by ordinary summability.
This does not construct a singular reader there.

## Dependency-closed paper proof

1. If `r` distinct primes divide `k`, their product divides `k`. For any
   one of those primes `p`, their remaining product divides the cofactor,
   so `k/p>=2^(r-1)`. For `a>0`, summing gives
   `sum_(p|k) (k/p)^(-a) <= r*(2^(-a))^(r-1) <= C_a`.
   Filtering an arbitrary finite prime set gives the stated bound.
2. Nonnegative finite-sum bounds prove each column is summable and its
   sum is at most `C_a`. For a summable nonnegative family `u(k)`, the
   complete nonnegative double sum is at most `C_a*sum_k u(k)`.
   Proven nonnegative Fubini permits reversal of the sums. Applying this
   to `u=abs(r)` gives the summable complex readout. No conditional
   interchange is assumed.
3. This readout cannot equal `c/p` for every prime with `c!=0`; multiplication
   by `c^-1` would make the reciprocal-prime family summable, contradicting
   the exact prime harmonic divergence theorem.
4. The kernel is tied to the actual physical weighted diagonal by
   `K_(2*sigma-1)(p,k) = p^(2*sigma-1) * k^(1-2*sigma)` on multiples of `p`.
   Thus the incidence output of the diagonal of any `T in D_sigma` is
   `p^(2*sigma-1)*Trace_sigma(T P_p)`, with the prime factor retained.
5. The previously proved physical exchange law has multiplier different
   from one for each prime in the convergence chamber. Prime pair
   cyclicity therefore gives `Trace_sigma(T P_p)=0`. The literal Green
   source has `Trace_sigma(Q P_p)=p^(-2*sigma)*Z_sigma`, where `Z_sigma>0`.
   Subtraction inside the actual admitted domain gives
   `p^(2*sigma-1)*Trace_sigma((T-Q)P_p)=-Z_sigma/p`.
   If its diagonal correction were summable, step 3 would contradict this.
6. For sharpness of the column threshold, take an integer equal to the
   product of arbitrarily many distinct primes. At `a<=0`, every selected
   kernel entry is at least one. This proves absence of a uniform column
   bound on that entire side, including the critical endpoint.

## Scope

This excludes summable diagonal repairs to the literal scalar ordinary-
integer Green source while retaining its fixed normal Gibbs reader.
The subsequent [full-source shell scalarization](route-l-full-gamma-shell-flattening.md)
constructs a specific bounded map from the complete rectangular Gamma source
to this scalar model with a summable correction, so the present obstruction
applies to that actual image. Its all-prime intertwining, Xi-jet fidelity,
and agreement with the required physical reader are not asserted.
RH remains unproved, and route L remains active.

The positive survivor is the full incidence mapping law and its sharp
parameter threshold. Unlike separate prime estimates, the column proof
controls overlap of every prime test on each source coordinate.

## Search and source audit

Deep/method searches were partial. The corpus supplied the literal
pairwise-prime coprimality mechanism in `Sieve.RoughCountTuran` and prime
harmonic divergence in `RouteRCofinalSieveHarmonicResidue`; the current
mathlib sources supplied relatively-prime finite products, nonnegative
Fubini, and geometric summability with a linear factor. No assumption
from another RH route enters the proof.

Broad recent-paper tests and their limitations are recorded under C19 in
`route-l-source-selected-completion-attack.md`. The permanent-pinch paper's
general residue rule is conjectural, while the second-order rigidity paper
requires an actual nonlinear constraint and a blocking stress. Neither is
used as a Lean premise or asserted to give the missing source comparison.

## Verification

- `lake env lean /tmp/route_l_prime_incidence.lean`: passed, no warnings.
- Targeted final `lake build GaloisForLFunctions.RHTower.DeningerGibbsPrimeIncidenceRepair`:
  passed; new module built, dependencies replayed. Import wired into `RHTower`.
- Complete 18-theorem audit through `/tmp/route_l_prime_incidence_axioms.lean`:
  only `propext`, `Classical.choice`, `Quot.sound`; no added axioms.
- `scripts/formal_tools.py lint`: passed, with existing file-size warnings.
- Source whitespace clean; no owned Lean process remains.
- No numerical experiment or full umbrella build.
