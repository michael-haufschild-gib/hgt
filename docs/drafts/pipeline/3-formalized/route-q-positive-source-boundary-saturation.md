# Route Q positive-source exact-boundary saturation

- **ID:** `route-q-positive-source-boundary-saturation`
- **Stage:** 3-formalized
- **Type:** THEOREM / source-specific no-go closure
- **Routes:** Q primary
- **Source:** separated continued prime--Gamma Cauchy packets

## Status labels

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`

## Theorem Q-PBS

Let `w` be the Xi--Hurwitz orientation vector, `e` its coordinatewise absolute-value companion,
and

```text
b₊ = (w+e)/2,   b₋ = (w-e)/2.
```

There exist sequences `P₊(n), P₋(n)` of actual finite pairwise-separated continued
prime--Gamma Cauchy packets such that

```text
evaluation(P₊(n)) -> b₊,       sourceEnergy(P₊(n)) -> 0,
evaluation(P₋(n)) -> b₋,       sourceEnergy(P₋(n)) -> 0,
sourceEnergy(P₊(n)) >= 0,      sourceEnergy(P₋(n)) >= 0.
```

This theorem has no premises. It also proves internally that if orientation energy `E` is
positive, every source energy in both sequences is strictly positive. If `E=0`, both boundary
points vanish and constant empty packets supply the sequences.

Therefore direct boundary saturation remains true under `not RH`: even genuine separated
prime--Gamma packets approach both exact null-boundary witnesses from the positive source-energy
side. Boundary saturation cannot be Route Q's missing RH-producing step.

## Heavy conjecture loop

### Q-PBS-1 — absolute companion may fail prime--Gamma source closure

**Conjecture.** The signed orientation vector is source-generated, but sign-forgetting may destroy
continued Cauchy source membership and make `b₊,b₋` inaccessible.

**Attack.** Orientation coordinate depends only on analytic zero support, not multiplicity copy.
Its absolute value is therefore constant on each finite multiplicity fiber. Regroup canonical
`lp.single` series by fibers. Each term is a scalar multiple of a fiber indicator already in the
continued prime--Gamma Cauchy Hilbert subspace; closedness sums the series.

**Verdict:** false. Lean proves unconditional continued-source membership of `e`.

### Q-PBS-2 — Hilbert closure may not contain actual separated packets

**Conjecture.** `b₊,b₋` may be abstract closure points inaccessible to finite collision-free
source packets.

**Attack.** Existing collision-removal theorem puts every algebraic continued-Cauchy vector in
closure of actual separated packet evaluations. Closure minimality contains the entire completed
continued-Cauchy Hilbert subspace, not only `w`. Thus it contains `w`, `e`, `b₊`, `b₋`, and all
linear perturbations used below.

**Verdict:** false.

### Q-PBS-3 — approximants may reach null boundary only through negative energy

**Conjecture.** Even if packet evaluations approach `b₊,b₋`, their source energies may be forced
negative, leaving positive-side incidence potentially RH-bearing.

**Attack.** For `t>0`, define

```text
u₊(t) = w/2 + (1/2+t)e,
u₋(t) = w/2 - (1/2+t)e.
```

Since `Jw=-w`, `Je=e`, and `||e||²=||w||²=E`, exact channel decomposition gives

```text
Q(u₊(t)) = Q(u₋(t)) = (t+t²)E.
```

When `E>0`, these are positive-energy source-closure points converging to `b₊,b₋`. Positivity of
`Q` is open. Intersect each positive neighborhood with a shrinking metric ball, then use
separated-packet closure to choose an actual packet in the intersection. Exact source identity
`sourceEnergy(P)=Q(evaluation(P))` makes every selected source energy positive. Evaluation
convergence and continuity of `Q` force source energies to zero.

**Verdict:** false. Positive-side boundary saturation is unconditional.

## Higher universal principle

**Source closure preserves incidence but not selection.** Passing from the algebraic
prime--Gamma Cauchy source to its Hilbert closure is rich enough to recover both fixed-sector
phases and open one-sided neighborhoods of both null witnesses. Thus adding “actual separated
packets,” “positive source energy,” or “exact boundary approach” does not restore lost arithmetic
orientation. Route Q is stuck because it needs a source-first cofinal rule selecting packets near
the anti-fixed target `w`, not existence near target-defined cone boundary.

This strengthens the earlier fixed-sector phase no-go: phase ambiguity is not confined to
abstract Hilbert vectors. Both phases are realized as limits of literal finite continued
prime--Gamma source packets from the same positive chamber.

## External novelty audit

Suzuki studies Hilbert spaces derived from the Weil distribution, screw-line norm formulations,
and model-space norm criteria for RH:

- <https://arxiv.org/abs/2301.00421>;
- <https://arxiv.org/abs/2209.04658>;
- <https://arxiv.org/abs/2301.05779>.

Targeted searches on 2026-08-16 found no external theorem identifying both Xi--Hurwitz exact
boundary witnesses as limits of actual pairwise-separated analytically-continued prime--Gamma
Cauchy packets with strictly positive finite source energies off RH. No priority claim is made;
novelty remains unverified.

## Gates

- [x] 0 -> 1: three hostile conjectures attacked; positive-side survivor isolated
- [x] 1 -> 2: dependency-closed proof and external novelty audit
- [x] 2 -> 3: unconditional Lean theorem, direct check, exact leaf build, axiom audit, umbrella wire
- [ ] 3 -> 4: independent significance audit and standalone exposition

## Lean closure

Module:
`formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationPositiveBoundarySourceSaturation.lean`.

Capstones:

- `xiHurwitzOrientationAbsoluteVector_mem_continuedCauchyHilbertSubspace`;
- `xiWeilContinuedCauchyHilbertSubspace_le_closure_separatedPacketEvaluations`;
- `xiWeilHilbertQuadratic_positiveTargetPlus`;
- `xiWeilHilbertQuadratic_positiveTargetMinus`;
- `exists_separatedContinuedCauchyPacket_sourceEnergy_pos_near`;
- `exists_positiveSeparatedPackets_tendsto_both_orientationBoundaries_of_energy_pos`;
- `exists_nonnegativeSeparatedPackets_tendsto_both_orientationBoundaries`.

Direct `lake env lean` and exact leaf `lake build` succeeded. Missing dependency `.olean`s were
built by exact leaf build only. Axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. Forbidden declaration scan is clean. Module is imported by `RHTower.lean`; no
umbrella or full-project build was run.

## Route consequence

Retire direct boundary saturation, including positive-side separated-source saturation, as an RH
producer. Live open core remains cofinal nonnegative recurrence along one unconditional
reconstruction converging to `w`, or an equivalent theta-specific reverse Cassini--Jensen source
sign law.

## Log

- 2026-08-16 — Absolute companion proved in continued prime--Gamma Cauchy Hilbert subspace.
- 2026-08-16 — Exact positive target energy `(t+t²)E` proved for both boundary phases.
- 2026-08-16 — Unconditional positive-side separated-source saturation proved in Lean.
- 2026-08-16 — Exact leaf built, axiom-audited, and wired without umbrella build.
