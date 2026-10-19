# No uniform coercivity constant for a fixed finite dilation horizon

- **Stage:** 5-failed
- **Type:** NO-GO with formalized positive closure; no contribution counted
- **Scope:** the actual clipped integer energies in `UniversalRamanujanCovarianceAndBiScaleRigidity.lean`.
- **Positive survivor:** [finite-horizon coercivity and its sharp doubling scale](../3-formalized/biscale-finite-horizon-coercivity-2026-10-18.md).

## Refuted statement

Fix any natural K. The proposed statement was existence of one real C such that, for every N and every f:ℕ→ℝ, some real center c satisfies

    sum_(1≤n≤N) (f(n)-c)^2 ≤ C * biScaleJointEnergy K N f.

`FiniteHorizon.not_uniform_window_coercivity` proves its negation for every K, with no analytic premise. The witness has frequency chosen by the existing simultaneous approximation theorem. Prime factorization controls every actual dilation; a telescoping additive estimate and proved integer quadrature control energy and variance.

At N=1024*(Q+1)^(d+2), where d counts odd primes at most K, the variance is at least N/16 and energy at most (384+65536K³)*(Q+1)^d. Thus a uniform C would bound a positive multiple of (Q+1)^2 for all Q, a contradiction.

## Exact positive insight and closure

Finite-window coercivity survives with explicit arithmetic control. Binary-parent descendant counts and native-edge comparison prove

    sum_(1≤n≤N) (f(n)-f(1))^2 ≤ 6*N*biScaleJointEnergy K N f,  K≥2.

The incomplete final binary generation is included. For K=2 this linear order is sharp on **every** N≥1024: an exact logarithmic resonance has joint energy≤384 and variance≥N/16. Hence every admissible constant C obeys

    N/6144 ≤ C,    while C=6*N is valid.

The dependency-closed paper proof and actual-object Lean proof are both complete. The formalized constants are exactly those displayed here. The optional tent refinement N/2048 on powers of two remains paper-only and is excluded from the closure claim and contribution count.

## Verification and novelty limits

All six leaves pass their direct `lake --old env lean -j 1 -o ... <source>` checks. The imported axiom audit passes with only `propext`, `Classical.choice`, `Quot.sound`; all leaves are wired and formal lint passes. Final evidence: `/tmp/bsu-100-positive-coercivity-leaf.log`, `/tmp/bsu-100-coercivity-classification-leaf.log`, `/tmp/bsu-100-coercivity-final-axioms.log`, `/tmp/bsu-100-coercivity-final-lint.log`.

The negative statement and positive proof closure do not establish novelty. Generic finite-prime recurrence/nonexpansion already exists in the corpus, and tree/planar-graph spectral bounds supply established neighboring mechanisms. The exact finite-prime quantitative comparison remains open on the survivor card. No new contribution is counted from this no-go or its supporting lemmas.
