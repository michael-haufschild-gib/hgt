# Arithmetic convergence domains and necessity of cofinal probes

Status: FORMALIZED. Dependency-closed paper proof, final leaf compile/export,
and all public axiom audits passed on 2026-10-09.

## Scope and source policy

Use only the local Lean corpus. No web, external papers, numerical experiments,
new analytic assumptions, heartbeat increases, or umbrella builds.

## Corpus audit

- `WeilLogShiftDomainBoundary.lean`: reciprocal-kernel weights realize exactly
  every finite open/closed symmetric potential domain.
- `WeilLogShiftConvergenceNoGo.lean`: a local coefficient construction realizes
  negative weights already zero below two; no reusable arbitrary-weight lift.
- `WeilLogShiftLocalExcessDomain.lean`: local excess plus lower-bounded actual
  probes characterizes convergence; cofinal sampling gives whole-line convergence.
- `WeilLogShiftReflection.lean`: reflection exchanges excess/deficit and the two
  infinite probe limits.
- `WeilLogShiftExcessControl.lean`: origin and sampled summability imply the exact
  finite actual-probe limit, including indices zero and one.

## Paper proof

For any signed weight v define lambda(n)=Lambda(n)+sqrt(n)*v(n). Its normalized
deviation is v(n) for n>=2 and zero otherwise. Removing two terms preserves
summability, so lambda realizes precisely v's potential domain. Nonpositive v
gives a minorant with identically zero excess; nonnegative v gives a majorant
with identically zero deficit. Apply this to plus/minus the existing reciprocal
weights to realize every finite open/closed symmetric arithmetic domain.

At any nontrivial integer-log probe inside the domain, the actual cutoff probe
converges to twice the difference of sampled and origin potentials. Outside,
the minorant probe tends to minus infinity and the majorant probe to plus
infinity, by the existing one-sided local convergence theorems.

Given a sequence of integer probes with log(m_j)<=B, take R=max(B,0) and the
closed-domain minorant. All sampled and origin potentials converge, so every
sampled actual probe has a finite limit and hence an eventual lower bound.
Choose an integer-log probe beyond R using `integer_log_probe_bounds`; its
potential diverges and its actual probe tends to minus infinity. Thus bounded
sampling fails even for zero excess. Conversely cofinal sampling suffices by
the corpus theorem. This proves cofinality is exactly the universal sampling
condition in the zero-excess class, not merely a sufficient hypothesis.

## Positive survivor / no-go closure

Exact arithmetic realizability of each finite symmetric domain, with finite
limits inside and prescribed signed infinite limits outside. The strongest
classification target is universal zero-excess sampling iff cofinality.

## Formal result

Leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftArithmeticDomain.lean`.
One definition and ten public theorems:

- `weilCoefficientLift`, `weilDeviation_coefficientLift`,
  `summable_coefficientLift_potential_iff`: arbitrary signed weights lift without
  changing their convergence domain.
- `exists_majorant_with_weight_potential_domain`,
  `exists_minorant_with_weight_potential_domain`: nonnegative weights lift with
  the appropriate one-sided defect identically zero.
- `exists_minorant_with_open_potential_domain`,
  `exists_minorant_with_closed_potential_domain`,
  `exists_majorant_with_open_potential_domain`,
  `exists_majorant_with_closed_potential_domain`: exact finite arithmetic
  domains, including empty and singleton domains at radius zero.
- `bounded_logShift_family_misses_minorant_divergence`: every bounded family
  has a zero-excess minorant with exact finite sampled limits and an eventual
  lower bound at every sample, but a nonsummable unsampled integer-log potential
  whose actual probe tends to minus infinity. Indices zero and one are covered.
- `cofinal_iff_zero_excess_probe_sampling`: cofinality iff universal recovery of
  whole-line convergence from individual eventual sampled lower bounds for
  every zero-excess coefficient sequence.

The existing local-excess/local-deficit divergence theorems and finite-limit
theorem apply to all newly realized domains; no additional analytic premise is
needed. The bounded-family witness includes its infinite actual-probe limit
explicitly in the formal theorem.

## Verification

- Final leaf compile/export: exit 0, no diagnostics. One initial deprecation
  warning was removed before the final compile.
- All eleven public declarations: exactly `[propext, Classical.choice, Quot.sound]`.
- Umbrella import wired; index refreshed; all eleven API entries inspected.
- Global lint: exit 1, seven unrelated modules unreachable from their umbrellas:
  `RHTower.CCMRiemannKernelBartaFarTail`,
  `RHTower.PaperCircleAdaptiveSelectionBudget`,
  `HTGeometry.CStarEnvelope`, `HTGeometry.CompactKernelAlgebra`,
  `HTGeometry.CompactKernelL2Representation`,
  `HTGeometry.CompactKernelRankOneDensity`,
  `HTGeometry.PaperFourierLLogL.Paths.Screen`.
  No error concerns the new leaf. These concurrent out-of-scope modules were
  not modified. No umbrella build, numerical experiment, new axiom, heartbeat
  increase, commit, push, or subagent was used.

The bounded-sampling route is retired separately with this exact positive
survivor in `../5-failed/weil-logshift-bounded-probe-sampling-no-go.md`.

No claim of external novelty or an RH proof.
