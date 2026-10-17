# Factorial ramp–tent full Weil Gram decoupling

- **Stage:** 1-in-progress
- **Route:** RW; exact arithmetic sources connected to WL factorial stencils.
- **Goal:** Remove the mixed-term sign/domain obligation for every linear combination of the actual factorial ramp and tent. Ultimate goal remains unconditional RH in Lean.
- **Prior result:** `../3-formalized/factorial-complete-form-coercivity-2026-10-18.md`.

## Plan

1. Establish the exact full spectral Weil quadratic formula on the two-dimensional source span.
2. Prove decay of its mixed coefficient from the existing unconditional factorial arithmetic and jump bounds.
3. Prove the tent diagonal dominates the source scale, then absorb the mixed term with an explicit vanishing error on the ramp diagonal.
4. Direct leaf checks, all-endpoint axiom audit, umbrella wiring, index and formal lint; keep the pure-ramp sign open unless separately proved.

## Corpus evidence

Whole-corpus queries `factorial ramp full Weil sign` (deep) and `compact Weil annihilator zeta Mellin null source` completed without partial results or errors. Semantic completeness was not measured; compiler metadata is not a substitute for direct checks. No directly applicable pure-ramp sign theorem was retrieved. The compact annihilator rigidity result requires separate hypotheses and does not identify this ramp with a null source. No zeta-kernel identification is assumed.

Applicable current source theorems: `factorialSource_mixed_forward`, `factorialSource_mixed_reverse`, `factorialSource_disjoint`, `factorialSource_combination_jump_integrable`, `factorialSourceRight_autocorr_tail`, `factorialSourceRight_jump_energy_lower`, `abs_integral_sourceFactorialCausal_archWeight_le`, `abs_fullPairing_sourceFactorialCausal_le`, and the new compact finite-jump spectral Weil identity.

## Conjecture and dependency-closed paper proof

Put N=n+1, L=factorialSourceLeft n, R=factorialSourceRight n, and Q(f)=Re of the literal full vonMangoldt Weil functional of f's autocorrelation. All sources cL+dR are compact, continuous and have finite jump energy, so the verified spectral identity applies without a regularity premise at the endpoint.

Let C be the even extension of sourceFactorialCausal N. Disjointness gives C(0)=0, and direct expansion of the autocorrelation gives

    H[cL+dR] = c² H[L] + d² H[R] + cd C.

The finite prime sum, polar integral and integrable jump term are linear on these profiles. Consequently, with A=Q(L), D=Q(R),

    Q(cL+dR) = c² A + d² D + cd M,
    M = -integral_(0,infinity) C(x) archLevySinhWeight(x) dx - 2 fullPairing(C).

Existing source estimates yield the unconditional bound

    |M| <= E_n := factorialSourceJumpError n
                    + 2 (10 log(4N+1)+3+1/(4N))/sqrt(N).

Since factorialJumpScale N=1000000 N^5, E_n=O(log(N)/sqrt(N)) and E_n tends to zero. This concerns the full signed Weil coefficient, retaining all prime atoms and both polar branches.

For the pure tent, 2 sourceFactorialWidth N <= 1/6 < log 2. Its autocorrelation therefore vanishes at every prime atom; its polar integral is nonnegative. Existing energy bounds give 6N <= H[R](0) <= 30N and J(R) >= 6 exp(-1/2) N log N. Hence

    D/N >= 6 exp(-1/2) log N - 30 |gammaBracket(0)|,

so D/N tends to +infinity and eventually D>=N>0. Complete the square, retaining half the tent diagonal:

    Q(cL+dR) >= c² (A - E_n²/(2N)) + (D/2) d².

The error E_n²/(2N) tends to zero. This bound is uniform in both real coefficients and assumes no positivity of A. The exact minimum in d is c²(A-M²/(4D)), attained at d=-cM/(2D).

All inequalities above follow from the displayed source bounds and elementary real algebra; Lean verification remains pending. This does not prove positivity of A, positivity of the span, or RH. The pure-ramp sign is the remaining arithmetic obstacle for this span.

## Status

Paper proof complete. No new Lean module written yet. Prior turn classified as progress: three verified coercivity modules and eighteen audited public theorems. No active Lean process at start of this card. No external novelty claim or numerical experiment.
