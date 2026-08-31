# Bounded cross-prime singular-graph lift no-go

- **ID:** CW-BSG-LIFT-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` shared HB/FZZ-P/RBH/PW-B Ward producer frontier
- **Statement:** No map continuous at the origin of the all-cross-prime Calderón--Witt `ℓ²` packet completion can reconstruct literal finite one-leg graph admission.

## Goal

Kill bounded irreducible cross-prime source coupling as missing common Ward producer. Proof chain attacked:

`bounded all-cross-prime source lift` → `source-faithful singular one-leg Gamma reporter` → `joint source/Gamma naturality` → `SharedFourRouteWardEndpoint` → HB unit cocycle gain + FZZ-P information equilibrium + PW-B partner balance + RBH leading balance → RH.

The theorem breaks first arrow unconditionally. It does not assert RH.

## Gates

- [x] 0 → 1 in-progress: source-pure statement and hostile limit test
- [x] 1 → 2 fully-proven: complete dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: Lean theorem, targeted build green, axiom audit clean
- [ ] 3 → 4 publication-ready: standalone exposition

## Paper proof `[PROVED HERE]`

Let `A(c)` be finite packet admission into ambient cross-prime `ℓ²`, and `G(c)` finite admission into one-leg graph completion. Corpus constructs source-normalized prime-two/right-prime Big-Witt rows `cₙ` with

`A(cₙ) → 0`, while `G(cₙ) → v`,

where vertical one-leg trace generator `v` is nonzero. Suppose `F` is continuous at `0` and `F(A(c)) = G(c)` for every finite packet `c`. Exactness at zero gives `F(0)=0`. Continuity and first limit give `F(A(cₙ)) → 0`; exactness and second limit give same sequence `F(A(cₙ)) → v`. Hausdorff uniqueness forces `v=0`, contradiction. Thus every exact reconstruction is discontinuous at origin. Continuous linear lifts are impossible as special case.

## Formal certificate

- Module: `GaloisForLFunctions.RHTower.DeningerBigWittCrossPrimeSingularGraphLiftNoGo`
- Capstone: `boundedCrossPrimeSingularGraphLiftRouteKilled`
- Sharp survivor: `crossPrime_oneLegGraph_reconstruction_not_continuousAt_zero`
- Explicit limit: `tendsto_crossPrime_oneLegGraph_of_finitePacket_reconstruction`
- Direct `lake env lean` check: PASS
- Targeted `lake build GaloisForLFunctions.RHTower.DeningerBigWittCrossPrimeSingularGraphLiftNoGo`: PASS (11486 jobs)
- Axioms for all five new theorems: `[propext, Classical.choice, Quot.sound]`
- Umbrella: imported by `GaloisForLFunctions.RHTower`
- Corpus search index: all declarations found
- Formal lint: new module clean; repository lint blocked only by unrelated pre-existing `HTGeometry.DominantConstantTermWild`, `HTGeometry.RittLevelThreeSeed`, and `sorry` in `RittLevelThreeSeed.lean:203`.

## Conjecturing loop

- **A — bounded graph-lift no-go:** proved, strengthened from linear to arbitrary origin-continuous maps.
- **B — bounded scalar trace no-go:** rejected as already in corpus.
- **C — global singular Gamma readout vanishing:** rejected as circular; corpus identifies it with RH.

## Novelty audit

Internal corpus search found ambient collapse and singular-graph convergence separately, but no graph-valued reconstruction no-go. Deninger's rational-Witt work (arXiv:1807.06400, arXiv:2508.05329) and Connes--Consani's semi-local Hilbert framework (arXiv:1910.14368) do not state this source-normalized all-cross-prime graph-lift obstruction. Novelty claim is limited to this exact theorem and architecture.

## No-go closure

- **Exact killing theorem/mechanism:** incompatible limits of same actual source-normalized finite packets under any origin-continuous exact reconstruction.
- **Strongest positive survivor:** exact reconstruction forces discontinuity at zero; topology change and singularity are necessary before all-cross-prime completion.
- **New insight:** singularity is required at source admission, not merely at final Xi-divisor evaluation.
- **Status:** paper proof dependency-closed and formalized without added axioms.

## Log

- 2026-08-31 — conjectured from corpus survivor, proved on paper, formalized, audited, and route retired.
