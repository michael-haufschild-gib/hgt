# Route E corpus-growth audit: critical Gibbs/sieve normalization wall (2026-08-06)

## Exact new bridge
For finite prime set P:
- a_P = sieveDensity P = ∏_{p∈P}(1-p⁻¹)
- B₁(P) = ∏_{p∈P}(1+p⁻¹), Route E r=1 Gibbs Mellin-energy Euler baseline
- C₂(P) = ∏_{p∈P}(1-p⁻²)

Exact: a_P B₁(P)=C₂(P)=sieveTrace(P,2)/sieveTrace(∅,2). Along every prime exhaustion, sieveTrace(P_n,2)→1, so a_{P_n}B₁(P_n)→sieveTrace(∅,2)⁻¹>0. Equivalently B₁(P)=sieveTrace(P,2)/(sieveTrace(∅,2)a_P).

Formalized unconditionally in RHTower/GibbsCriticalSieveNormalizationWall.lean:
- gibbsCriticalEulerBaseline
- sieveDensity_mul_gibbsCriticalEulerBaseline
- sieveTrace_empty_two_mul_criticalNormalization
- tendsto_criticalSieveNormalization
- gibbsCriticalEulerBaseline_eq_sieveTrace_div
Axioms: propext, Classical.choice, Quot.sound only. Targeted build 8864/8864.

Paper card: docs/drafts/pipeline/3-formalized/route-e-critical-gibbs-sieve-normalization-wall.md.
Active Route E card and rh-current-frontier-map updated.

## Hostile consequence
This closes only regular p⁻²/Hilbert–Schmidt layer. Raw r=1 Euler growth is exactly reciprocal sieve-density growth times a finite nonzero regular factor. Multiplying by a_P removes growth but erases source-normal mass; dividing back restores it. Existing prime-valuation conditioning no-go makes amplification exact: unnormalized a_P/p becomes normalized 1/p and is nonsummable.

Therefore prime-sieve density telescoping, determinant convergence, HS vacuum collapse, or generic SeminormCompletion cannot imply normalized Route E current bound. Claiming they do is theatre.

## Frontier
OPEN-SOURCE-001 remains open. Gibbs hard core remains WEIGHTED-PRIME-DILATION-INCREMENT-CANCELLATION. Sharpened possible form: explicit source-derived signed first-trace/Bockstein countertransport from parity–energy covariance E-COV, cancelling normalized 1/p principal transition across alternating finite volumes before positive norm, leaving already-controlled p⁻² remainder. Must be uniform at moving antiscale t≈1/log max P and non-circular.

Hall: a_{P_{j-1}}/p_j are canonical scalar weights summing to one, but no moving-window lift to R_X^gr, collision-quotiented interval Hall, or cross-anchor incoming load. They do not close Hall.

Prime-sieve SOURCE-NORMAL CONTRACTIVE POLAR TRANSGRESSION is a separate RH-bearing conjecture; normalization-amplification shows its missing estimate is not supplied by summable unnormalized transitions.

No external literature used, per user instruction.