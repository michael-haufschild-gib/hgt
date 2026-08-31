# Gamma-sewn synchronized-recovery moving-support rigidity

- **ID:** REC-UD
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** corpus-derived from exact synchronized recovery quotient and REC-Q2
- **Statement:** If `X=x∑_{p∈P}log p`, then `1-X-3X² ≤ R_{ν,P}(x) ≤ 1`; consequently every moving-support schedule with `X→0` has recovery ratio tending to one.

## Goal

Decide whether fixed-support quadratic recovery curvature can become actual source damping on a
cofinal moving prime support without losing coefficient-faithful completion.

## Gates

- [x] 0 → 1 in-progress: corpus search found exact quotient, strict contraction, and quadratic tangency, but no support-uniform law
- [x] 1 → 2 fully-proven: uniform finite-product proof in the total prime phase `X`
- [x] 2 → 3 formalized: targeted leaf build and axiom audit pass
- [ ] 3 → 4 publication-ready: standalone exposition and external novelty audit

## Result

The estimate is independent of support cardinality and prescribed positive density `ν`. It uses
the exact chord quotient, a uniform bound on the Gamma quadratic-defect gain, and finite
Weierstrass product control. Thus it passes from every finite stage to arbitrary moving supports
without any RH-strength infinite-tail estimate.

If `x_N∑_{p∈P_N}log p→0`, then `R_{ν,P_N}(x_N)→1`. Therefore synchronized recovery cannot provide
nonzero unnormalized order/damping while retaining the small-total-phase completion used for
coefficient-faithful Ward landing. Any surviving recovery-based Frankenstein route must operate
in a non-small total-phase regime and prove a different landing theorem there.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.GammaSewnSynchronizedRecoveryMovingSupportRigidity`
- Main theorems:
  - `gammaSewnSynchronizedRecoveryRatio_uniformLower_totalPrimePhase`
  - `gammaSewnSynchronizedRecoveryRatio_mem_totalPrimePhaseBounds`
  - `tendsto_gammaSewnSynchronizedRecoveryRatio_movingSupport_of_totalPrimePhase`
- Targeted leaf build: PASS
- Axioms: `propext`, `Classical.choice`, `Quot.sound`

## No-go closure

- **Exact killing mechanism:** total prime phase tending to zero squeezes ratio to one uniformly in moving support.
- **Strongest positive survivor:** REC-Q2 diverging normalized curvature remains valid; nontrivial damping can only occur when total phase does not vanish.
- **New insight:** frontier is not a stronger small-aperture remainder. It is a coefficient-faithful non-small-total-phase landing, or a different nonmultiplicative channel.
- **Status:** dependency-closed Lean theorem, built and axiom-audited.

## Log

- 2026-08-31 — conjectured after corpus-wide duplicate/no-go search; proved, formalized, built, axiom-audited, and wired.
