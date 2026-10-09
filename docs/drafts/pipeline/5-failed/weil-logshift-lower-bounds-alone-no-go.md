# Lower bounds on all probes do not force potential convergence

Status: [FAILED ROUTE CLOSED; POSITIVE SURVIVOR FORMALIZED]
Date: 2026-10-09
Source policy: our Lean corpus only; no web or external papers.

## Failed proposal

Drop local positive-excess moment control and recover signed sampled-potential
summability from eventual lower bounds on the actual probes. Even requiring
these lower bounds at every nontrivial integer probe does not rescue the claim.

## Exact obstruction

Take lam(n)=Lambda(n)+sqrt(n)*exp(2*pi*n). It majorizes von Mangoldt and has
identically zero normalized deficit. For every m>=2 the signed potential at
log m is nonsummable, because its exponential rate 2*pi exceeds 2*pi/m. Yet
the actual real-cutoff probe tends to plus infinity and is eventually
nonnegative on integer cutoffs. The same sequence defeats every probe at once.

Lean theorem:
`RHTower.exists_majorant_all_logShift_probes_atTop_not_summable`
in `formal/GaloisForLFunctions/RHTower/WeilLogShiftReflection.lean`.
The more precise rate theorem is
`RHTower.exponential_majorant_logShift_probe_atTop`: any positive exponential
deviation with rate rho>2*pi/m sends that fixed probe to plus infinity.
No critical-rate equality is claimed.

## Strongest positive survivor

Coefficient reflection R(lam)=2*Lambda-lam is an involution, negates normalized
deviation, exchanges excess and deficit, and satisfies the exact identity

  Q_lam(L,c)+Q_R(lam)(L,c)=2*W(L,c).

For each m>=2 this yields the dual domain classification:

- Signed sampled summability iff finite local excess moment plus an eventual
  integer-cutoff lower bound (previous LocalExcessDomain leaf).
- Signed sampled summability iff finite local deficit moment plus an eventual
  integer-cutoff upper bound (new Reflection leaf).
- Finite local excess with nonsummable signed sample forces the real-cutoff
  probe to minus infinity; finite local deficit instead forces plus infinity.
- Signed sampled summability gives the exact finite limit
  2*(psi(log m)-psi(0)), without a separate origin hypothesis.

The new insight is the necessary pairing between the controlled one-sided
moment and the direction of the probe bound. Zero deficit cannot substitute
for excess control in a lower-bound criterion; the explicit majorant proves it.
The counterexample also shows why an increasing probe value is not evidence
of convergence of its full signed potential.

Paper status: dependency-closed proof recorded in
`3-formalized/weil-logshift-reflection-duality.md` and the preceding local-excess
card. Lean status: exact reflection, dual convergence criterion, divergence,
and counterexample all compiled/exported in the Reflection leaf; all eleven
public declarations use only `propext`, `Classical.choice`, `Quot.sound`.
Umbrella wired and API indexed. Global lint remains affected by three unrelated
umbrella omissions listed on the positive proof card.

## Scope boundary

This rejects a convergence inference, not an RH route or a general positivity
statement. Both one-sided moments divergent is unclassified here. No external
novelty claim or unsupported analytic premise is used.
