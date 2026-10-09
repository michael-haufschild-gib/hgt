# Reflection duality and the lower-bounds-alone obstruction

Status: [FORMALIZED; GLOBAL LINT HAS THREE UNRELATED UMBRELLA ERRORS]
Date: 2026-10-09
Source policy: our Lean corpus only; no web or external papers.

## Objective and plan

Reflect coefficients about von Mangoldt to dualize local excess control. Prove
the local deficit/upper-bound convergence criterion and demonstrate why lower
bounds alone cannot recover convergence, even at every nontrivial probe.

1. Audit normalized deviation, truncated potential identity, local excess
   divergence, and the exponential threshold. Check finite-index exceptions.
2. Formalize reflection as an involution, excess/deficit exchange, and the exact
   probe sum identity.
3. Derive divergence to plus infinity under finite local deficit and the exact
   local-deficit plus upper-bound criterion.
4. Construct a positive exponential majorant whose every nontrivial probe tends
   to plus infinity despite nonsummable sampled potentials. Record the failed
   lower-bound-only route and its positive survivor.
5. Compile/export, audit all public declarations, wire/index/lint, promote the
   positive card, save memory, clean owned scratch. No critical-endpoint claim.

## Dependency-closed paper proof

Define R(lam)(n)=2*Lambda(n)-lam(n). Then R is an involution and normalized
deviation changes sign: a_R=-a. For n<2 both deviations vanish by definition;
for n>=2 this is linear algebra over the same sqrt(n) denominator. Thus excess
and deficit exchange. Truncated potentials negate termwise (their sums have
finite support). The exact probe identity gives

  Q_lam(L,c)+Q_R(lam)(L,c)=2*W(L,c).

At c=log m the right side tends to zero. If the original deficit moment is
finite and its signed sample nonsummable, the reflected positive-excess moment
is finite and its signed sample nonsummable. The existing local excess theorem
forces Q_R->-infinity. A fixed lower bound on W and the sum identity give
Q_lam->+infinity. Conversely signed sample convergence gives deficit convergence
by applying positive-part control to the reflected signed sample, and gives a
finite probe limit. Therefore, for m>=2, signed sampled summability is exactly
local deficit summability plus an eventual integer-cutoff upper bound.

For the obstruction set lam_rho(n)=Lambda(n)+sqrt(n)*exp(rho*n). Normalized
deviation is exp(rho*n) for n>=2 and zero below; deficit is identically zero.
If rho>2*pi/m, the corpus exponential-threshold theorem makes the sampled
potential nonsummable; deleting the first two terms does not alter summability.
The new local-deficit theorem then forces this probe to plus infinity, so it
is eventually bounded below despite divergent potential.

Choose rho=2*pi once for all m>=2. Since 2*pi/m<2*pi, every nontrivial probe
tends to plus infinity and has divergent sampled potential. Thus even lower
bounds at ALL probes cannot imply convergence when positive-excess moment
control is dropped. The positive survivor is the exact reflection identity and
the dual one-sided domain classification. Both must be formalized before the
failed route is retired.

## Corpus audit

Direct lexical search: 2226 declarations, 345 modules, 581 eligible entries;
cached output has no partial/coverage fields. Existing coefficient reflection
was not found among the local log-shift results. Relevant definitions and
identities are in WeilFullConeNearNullPositiveDefinite, WeilLogShiftExcessControl,
WeilLogShiftLocalExcessDomain, and WeilLogShiftLocalDecayThreshold. Existing
reflection hits concern other spectral variables and are not used here.

## Verification

- `WeilLogShiftReflection.lean` compiled/exported directly with
  `lake --old env lean <leaf> -o <local olean>`; exit 0, no diagnostics.
- Eleven public declarations: reflection definition/involution, deviation sign
  reversal, excess/deficit exchange, truncated potential negation, exact probe
  sum identity, local-deficit divergence, dual domain equivalence, exponential
  divergence above the local rate, and the all-probe counterexample.
- All eleven public declarations passed scratch `#print axioms`; only
  `propext`, `Classical.choice`, and `Quot.sound` occur.
- Umbrella import added. Index refresh succeeded and all eleven public API rows
  were inspected. Scoped `git diff --check` passed.
- Global formal lint exited 1 on three unrelated modules unreachable from their
  umbrellas: `RHTower.PaperCircleSplitCharacterPosterior`,
  `HTGeometry.DiscreteCrossedProductCStar`, and
  `HTGeometry.PrimeTranslationModularFlow`. These sources/imports were not
  modified. The preceding CCM umbrella error no longer appears.
- The failed lower-bounds-alone route and its formalized positive survivor are
  recorded in `5-failed/weil-logshift-lower-bounds-alone-no-go.md`.
- All owned jobs exited. Owned `/tmp/hgt-weil-probe-reflection-*` scratch files
  were removed after recording evidence. No numerical experiments, new axioms,
  unproved analytic inputs, heartbeat increases, full/umbrella builds, commits,
  or subagents.

All scoped steps are complete. Reflection gives an exact symmetry of the
arithmetic probe contribution and a second sharp one-sided domain criterion.
The all-probe exponential majorant closes the lower-bounds-only route while
preserving the exact local-moment replacements on both sides.

## Remaining boundary

When both local excess and local deficit moments diverge, neither one-sided
criterion applies. This increment does not classify the resulting probe
behavior or assert the existence of bounded probes with nonsummable potentials.
That case requires a new corpus audit and paper argument. The separate
pure-exponential critical endpoint is now settled by
`WeilLogShiftCriticalEndpoint.lean`: equality diverges, and the actual positive
majorant probe tends to plus infinity already at rho=2*pi/m.
