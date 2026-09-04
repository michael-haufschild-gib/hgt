# Moving-Hermite all-depth classification no-go

- **ID:** moving-hermite-all-depth-classification-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** local squarefree-half multiplicity-parity ladder route
- **Statement:** No canonical fixed-anchor boundary-Hermite depth schedule can be both Euler-admissible and locally bounded along a cofinal pole-factor schedule.

## Goal

Close the last oscillatory-depth residue of the canonical point-Hermite representation and extract
the exact surviving design constraint for any successor transition mechanism.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted build green, axiom audit passed
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact claim

[PROVED HERE] For arbitrary `depth kappa : ℕ → ℕ`, if `kappa N→∞`, then

`N ↦ boundaryHermiteJetCounterterm N (depth N)`

cannot be both `SquarefreeHalfCountertermAdmissible` and locally bounded after insertion into
`poleClearedFirstTraceCountertermScheduledApprox`.

No monotonicity, regular variation, or one-sided asymptotic condition on `depth` is assumed.

## Complete proof

Split on whether the range of `depth` is bounded.

If `depth N≤B` for every `N`, then eventually

`depth N ≤ N/54`.

The existing bounded-slope point-Hermite theorem therefore contradicts local boundedness directly.

Suppose instead that the range is unbounded. For every `j`, choose `phi j` with

`j≤depth(phi j)`.

This choice automatically satisfies `depth(phi j)→∞`. It also satisfies `phi j→∞`: for a fixed
cutoff bound `A`, let

`M_A = Σ_{m<A} (depth m + 1)`.

If `j≥M_A` but `phi j<A`, then the selected inequality and the summand indexed by `phi j` give

`M_A ≤ j ≤ depth(phi j) < depth(phi j)+1 ≤ M_A`,

a contradiction.

Now restrict the original corrected approximants to indices `phi j`. Analyticity and local
boundedness are inherited pointwise. Since `phi j→∞`, Euler compact-open convergence is inherited
by composition. Since `depth(phi j)→∞`, every fixed derivative at the Hermite anchor is eventually
exactly zero by the unbounded-depth jet theorem.

Vitali therefore produces a holomorphic limit on `rightHalf` whose complete jet at `6/11` is zero.
Analytic germ determinacy and connectedness make the limit identically zero. Euler convergence at
`2` makes it equal to `poleClearedFirstTraceSourceLimit 2`, whose square is the nonzero value
`(2-1) exp(coronaPrimeZeta 2)`. Contradiction.

## Hostile audit

- The selected `phi` need not be monotone or injective; the finite-prefix sum proves exactly the
  cofinality required to compose all `atTop` convergence statements.
- Restriction is applied to the original approximants at cutoff `phi j`; it does not replace their
  Dirichlet cutoff by `j`.
- Original local boundedness is uniform in every index, hence immediately bounds the subsequence.
- Original Euler compact-open convergence composes with every cofinal index map.
- Bounded and unbounded range are exhaustive constructively after classical choice already used by
  the analytic corpus.

## No-go closure

- **Exact killing theorem/mechanism:** Bounded depth is too shallow to cancel interior pole-factor
  growth; unbounded depth contains a cofinal subsequence annihilating every fixed anchor jet and
  therefore forces an impossible flat Euler-faithful Vitali limit.
- **Strongest positive survivor:** The full canonical fixed-anchor point-Hermite class is terminal.
  Any viable correction must fail at least one defining feature: fixed anchor, initial Taylor
  segment, exact increasing jet annihilation, or point-local interpolation.
- **New insight:** Oscillation does not interpolate between low- and high-depth regimes. Its bounded
  part is killed by pole growth; its unbounded part already contains the flatness obstruction.
- **Status:** Complete dependency-closed paper proof and Lean formalization. Capstone:
  `not_admissible_and_locallyBounded_boundaryHermiteJetCounterterm`.

## Lean verification

- Module:
  `formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfMovingHermiteUnboundedDepthNoGo.lean`
- Cofinal extraction:
  `exists_cofinal_high_depth_subsequence`.
- Unbounded oscillatory-depth theorem:
  `not_admissible_and_locallyBounded_boundaryHermiteJetCounterterm_of_depth_range_unbounded`.
- All-depth capstone:
  `not_admissible_and_locallyBounded_boundaryHermiteJetCounterterm`.
- Direct check:
  `lake env lean GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfMovingHermiteUnboundedDepthNoGo.lean`
  — passed.
- Targeted build:
  `lake build GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfMovingHermiteUnboundedDepthNoGo`
  — passed, `13066/13066` jobs.
- Axiom audit for extraction, unbounded-depth theorem, and all-depth capstone:
  `[propext, Classical.choice, Quot.sound]` only.
- Umbrella:
  `formal/GaloisForLFunctions/RHTower.lean` imports module.

## Log

- 2026-09-04 — extracted cofinal high-depth subsequence; bounded/unbounded dichotomy completed; promoted directly to Stage 2.
- 2026-09-04 — formalized cutoff-preserving subsequence transport and all-depth dichotomy; promoted to Stage 3.
