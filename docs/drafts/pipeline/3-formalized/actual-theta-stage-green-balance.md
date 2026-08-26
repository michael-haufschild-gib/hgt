# Actual Theta Stage Green Balance

- **ID:** actual-theta-stage-green-balance
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** user-directed Hedenmalm actual-stage frontier
- **Statement:** Every actual signed theta stage has an exact complete Green boundary whose modal charge equals `-2 Im(mu)` times strictly positive canonical theta energy; modewise neutrality is exactly eigenvalue realness, while fixed-metric adjointness is exactly cancellation of the pinned rank-two current by the stage correction.

## Goal

Identify source-only boundary law available for actual coefficient-faithful finite stages, without
Xi zero selection, and isolate exact extra assertion needed for real finite divisors.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `inner_thetaSourceSignedStageGreenBoundary_eigen`, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Write the actual stage as `A_k = -K + E_k`, where `E_k → 0` in operator norm. For canonical
theta metric `G`, fixed source operator `K`, and pinned rank-two current `C`, expand

`G A_k - A_k† G + i C = G E_k - E_k† G`.

Define the right side as stage Green remainder `R_k` and complete boundary as `C + i R_k`.
Then

`G A_k - A_k† G = -i (C + i R_k)`.

Pairing this identity with an eigenmode `A_k f = mu f` gives

`<B_k f,f> = -2 Im(mu) <Gf,f>`.

Pointwise positivity of reciprocal quantile speed makes `G` positive. Its already-proved
injectivity and the positive-operator kernel law give `<Gf,f> != 0` for `f != 0`; therefore
`<B_k f,f> = 0` if and only if `Im(mu) = 0`.

Continuity of multiplication and adjoint gives `R_k → 0`, hence `B_k → C`. Since `C ≠ 0`,
`R_k = iC` cannot hold eventually. Algebraically, that equality is equivalent to fixed-metric
adjointness of `A_k`.

`[PROVED HERE]` Every step uses existing source operator convergence, exact fixed-source Stokes
commutator, bounded-operator algebra, and Hausdorff uniqueness of norm limits.

## No-go closure

- **Exact killing theorem/mechanism:** `thetaSourceSignedPulledOperator_not_eventually_thetaMetricAdjoint`; equivalently, `thetaSourceSignedStageGreenRemainder_not_eventually_pinnedGreen`. Vanishing correction commutators cannot cancel a fixed nonzero pinned current eventually.
- **Strongest positive survivor:** Exact complete Green boundary and modal Stokes law at every actual stage, strict theta-metric energy, neutrality iff eigenvalue realness, exact adjointness/cancellation classification, and operator-norm convergence to pinned rank-two boundary.
- **New insight:** Actual stages are asymptotically rank-two Green systems, not exact rank-two-neutral systems. Missing real-divisor input is exact modewise vanishing of complete boundary charge, not approximation, trace zero, or escape of exceptional poles.
- **Status:** Paper proof dependency-closed; Lean module `GaloisForLFunctions.RHTower.HedenmalmThetaActualStageGreenBalance`; targeted build and axiom audit pass.

## Log

- 2026-08-26 — hostile conjecture loop: fixed positive-metric adjointness falsified; positive escaping and Krein variants rejected as divisor-changing or reality-insufficient.
- 2026-08-26 — exact Green balance, modal alternative, adjointness classification, and non-eventual cancellation formalized.
