# BAG — disc-uniform Carlson tail, typical-height pair recurrence, head-zero obstruction

- **ID:** BAG-disc-uniform-carlson-tail-typical-height-recurrence-2026-10-20
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Read-only current frontier, BAG (`docs/reports/rh-current-frontier-map.md`); local Lean corpus.
- **Statement:** Carlson's unconditioned tail law holds uniformly on every right-strip disc at density-one heights; along the finite head's almost periods, ζ self-returns on the translated disc at density-one base heights; where the partial sum vanishes inside the disc, finite-head return heights are tail-bad up to density zero.

## Goal

The BAG ledger lists as open: "align these [density-one Abel-centered tail] heights with finite-head returns uniformly on a right-strip disc" and records that Carlson's vertical `L²` mean "does not supply conditioned tail control or uniform disc recurrence". This card connects existing corpus components to settle the *uniform-disc* half unconditionally, to extract the positive survivor (typical-height pair recurrence of the actual ζ on discs), and to prove the exact mechanism behind the remaining *conditioned* half (zeros of the partial sum force the conditioned loss).

Not claimed: fixed-base-height recurrence of ζ (RH-sufficient via `riemannHypothesis_of_zetaDiscRecurrent`; refuted around off-line zeros by `exists_zetaSelfReturn_density_zero`), nor any payment of the Abel base-point pole `M^(1−z)/(1−z)`. The route stays live; the ledger is not edited.

## Components connected

1. `RHTower/ZetaSuperlinearTruncation` — explicit arbitrary-order Euler–Maclaurin scale `zetaTruncationErrorScale`; `RHTower/ZetaSuperlinearCutoff` — vanishing of that scale and of the band mean-square error along `superlinearCutoff`.
2. `RHTower/ZetaDirichletBandMeanSquare`, `RHTower/CarlsonZetaMeanSquare` — sharp band mean squares and tail mass.
3. `HTGeometry/HolomorphicBallMeanSq` — planar holomorphic mean-square inequality for entire functions; applied to the entire function `(s − 1)(ζ(s) − head_M(s))` built from Mathlib's `riemannZeta_residue_one` and the removable-singularity criterion.
4. `HTGeometry/BohrFiniteRecurrence`, `HTGeometry/AlmostPeriodicReturnDensity` — positive lower density of simultaneous almost periods of finitely many logarithmic phases.
5. `RHTower/ZetaStrongRecurrenceReceiver`, `RHTower/ZetaFixedSigmaDensity` — zero transport by the minimum-modulus principle and `o(T)` zeros right of a fixed abscissa.
6. `RHTower/BagchiCarlsonCenteredTailBridge` — Abel-centered tail and its uniform fractional-part bound.

## Theorems (all unconditional; axioms `propext`, `Classical.choice`, `Quot.sound` only)

Module `RHTower/ZetaDiscUniformCarlsonTail.lean` (wired into `RHTower.lean`):
- `zetaTruncationErrorScale_le_of_le`: the truncation scale at `σ ∈ [σ₀,1]` is at most `2^(2m+2)` times the scale at `σ₀`.
- `eventually_uniform_dyadic_zetaDirichletTail_meanSquare_le`: the dyadic mean square of `ζ − head_M` is eventually `≤ V(2·tailMass(M,σ₀) + η)` uniformly for `σ ∈ [σ₀,σ₁] ⊂ (1/2,1)`.
- `differentiable_zetaPoleFilled`, `differentiable_zetaTailPoleWeighted`: `(s−1)ζ(s)` and `(s−1)(ζ(s)−head_M(s))` are entire.
- `normSq_zetaTailFun_le_integral_ball`: at every point of `closedBall c r + iτ`, `|ζ − head_M|²` is at most `(1 + r/(1−(Re c+2r)))²/(πr²)` times the planar mean square on `ball c (2r) + iτ`.
- `volume_discTailBadSet_window_le`: Tonelli–Markov bound on the bad heights in `[V/2, V]`.
- `eventually_volume_inter_Icc_le_of_dyadic_window`: window density `≤ β` gives prefix density `≤ 2β + κ`.
- `eventually_eventually_volume_discTailBadSet_le` (**disc-uniform Carlson tail law**): for `closedBall c (2r) ⊂ {1/2 < Re < 1}` and `ε, δ > 0`, for all large `M`, `{τ ∈ [0,T] : ∃ z ∈ closedBall c r, |ζ(z+iτ) − head_M(z+iτ)| ≥ ε}` has measure `≤ δT` for all large `T`.
- `eventually_eventually_volume_not_mem_abelCenteredZetaTailReturnSet_le`: the complement of the disc-uniform Abel-centered return set `abelCenteredZetaTailReturnSet M (closedBall c r) ε` has density `≤ δ` for all large `M`.

Module `RHTower/ZetaTypicalHeightPairRecurrenceAndHeadZeroObstruction.lean` (wired into `RHTower.lean`):
- `exists_pos_density_headPhaseReturnSet`: simultaneous `θ`-almost periods of `n^{-id}`, `n ≤ M`, have positive lower density; `norm_edPoly_one_Icc_shift_sub_le`: along such a `d` the head moves by `≤ Mθ` on `Re w ≥ 0`.
- `exists_headPhaseReturnSet_zetaReturn_typicalHeight` (**typical-height pair recurrence**): for every disc and `ε, δ`, there are `M`, `θ > 0` such that each `d ∈ headPhaseReturnSet M θ` lies in `zetaReturnSet (closedBall (c + iτ₁) r) ε` for all `τ₁ ∈ [0,T]` outside a set of measure `≤ δT`; `exists_pos_density_zetaReturn_typicalHeight` packages the positive-density set `E` of such `d`; `exists_zetaReturn_shift_ge_on_translate`: ε-return shifts `d ≥ R` exist on some translate of every disc.
- `eventually_volume_window_le_of_forces_zero`, `eventually_volume_inter_Icc_le_of_forces_zero`: shift sets forcing a zero of ζ in a translated right-strip disc have density zero (abstract form of the density-zero law).
- `exists_zero_of_mem_poleShiftedReturnSet`, `eventually_volume_poleShiftedReturnSet_le` (**head-zero obstruction**): if `head_M(ρ₀) = 0` and `|head_M| ≥ m` on the boundary circle, the pole-shifted return set `{τ : sup_disc |ζ(z+iτ) − head_M(z)| < ε}`, `ε ≤ m/2`, has density zero.
- `eventually_volume_edPolyReturnSet_le_discTailBadSet_add`: under the same hypotheses, `|edPolyReturnSet(ε/2) ∩ [0,T]| ≤ |discTailBadSet(ε/2) ∩ [0,T]| + κT` eventually — finite-head return heights are tail-bad up to density zero.
- `exists_headIsolatingDisc`: isolating discs with a positive boundary floor exist around every point of the strip (partial sums are not identically zero), so the obstruction hypotheses are satisfiable at every zero of a partial sum in the strip.

## Insight for the route

- The *unconditioned* half of the open alignment problem is closed: Carlson-good heights are disc-uniform and have density one, also for the Abel-centered tail.
- The *conditioned* half (common heights of head returns and tail smallness) is not a missing estimate but an obstruction with a mechanism: whenever the partial sum `head_M` has a zero inside the disc, the Kronecker return set of the head and the Carlson-good set are disjoint up to density zero, because a common height would transport the head's zero to a zero of ζ at that height, and such zeros are `o(T)`. A proof of fixed-height self-return on such a disc must therefore use heads without zeros in the disc or a different head/tail split; the Abel pole is the analytic trace of the same fact.
- The positive survivor is the pair law: ζ is recurrent on discs of the strip at typical base heights along the head's almost periods, with density-one base heights for each almost period. Fixed-height recurrence (Bagchi's criterion) remains exactly the open RH-equivalent core.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: the paper proof is the module docstrings; dependency-closed on corpus + Mathlib
- [x] 2 → 3  formalized: both modules pass `lake --old env lean -j 1 -o …` (exit 0, no warnings), `#print axioms` standard, wired into `RHTower.lean`; no umbrella build run (policy)
- [ ] 3 → 4  not applicable (no stage 4; RH-only policy)

## Log
- 2026-10-20 — created; both modules written, compiled, audited (`#print axioms`), wired; lint run; one declaration renamed (`im_sub_abs_lt_of_mem_ball`) to avoid a fully-qualified name collision with `CHMDMasslessContinuationPieces.abs_im_sub_lt_of_mem_ball`.
