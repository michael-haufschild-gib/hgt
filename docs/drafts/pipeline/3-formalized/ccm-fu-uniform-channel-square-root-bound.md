# CCM-FU: uniform square-root channel bound and initial reserve scale

- **Stage:** 3-formalized
- **Parent:** [adaptive prime ceiling](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Type:** uniform arithmetic source bound and scale of initial correction reserve
- **Boundary:** this controls individual channels and a balanced initial late block, not the complete Möbius sum.

## Exact source proof

Retaining the half-logarithmic endpoint in the Stirling upper bound gives `log(N!)<=N log N-N+(log N)/2+1` for every N>=1. For s=floor(sqrt(N)), split the exact smooth divisor-hyperbola remainder into

`[log(N!)-N log N+N-H_s] + [N(log N-2 log s)-N+s^2] + [s-2N(H_s-log s-gamma)]`.

The three brackets are at most 2, 4 and 1, respectively. The first uses the retained half-log endpoint, which cancels the harmonic logarithm. The second uses `s^2<=N<=s^2+2s` and `log x<=x-1`. The third uses the half-reciprocal harmonic error. The zero cutoff is checked separately. Thus `smoothRemainder(N)<=7` at every natural cutoff.

The centered modular Abel channel is nonpositive. Telescoping the square-root clock gives `0<=K_1(M)<=7 sqrt(M)`. Exact clipped homothety transfers this same bound to every unsigned channel K_d(M): the convex interpolation weights are defined by that same square-root clock, so no endpoint loss is added.

The initial retained head is K_1(M), so its square is at most `49M`. This is below every positive multiple of M^2 eventually.

The complete initial correction also removes isolated singleton squares. Let L consist of primes p<M with M<=2p, and suppose its resulting head is at least `-sqrt(M)`. Its consumed unsigned mass t satisfies `t<=8 sqrt(M)`. Each late component lies in `[0,sqrt(M)]`, so `sum_(p in L) C_p^2<=sqrt(M)*t<=8M`. The exact nonempty-energy law therefore gives

`Q_empty-Q_L=h_empty^2-h_L^2+sum_(p in L)C_p^2<=57M`.

For every epsilon>0, this complete released energy is at most `epsilon M^2` eventually, uniformly over every such L. Both previously formal initial balancing constructions meet this head condition. Their complete reserve is thus only linear, including the removed singleton squares. A continuation must obtain any larger required reserves from the actual paired source. This does not assert that a quadratic reserve is necessary, supply a lower bound for the original diagonal, or decide PE4 or SD1.

## Lean certificate and verification

`RHTower.DivisorUniformSquareRootBound` contains nine public theorems. The main declarations are `divisorUnsignedDilationChannel_le_seven_sqrt`, `mobiusDivisorSelectionHead_empty_sq_le_linear`, `mobiusDivisorInitialLateBlock_release_le_linear`, and `eventually_mobiusDivisorInitialLateBlock_release_le_quadratic_multiple`. The latter is uniform over every admissible block.

The complete scratch and exact leaf checks passed with `lake env lean`, using existing required oleans. The leaf is wired once in `RHTower.lean`; no full, dependency or umbrella build was run. All nine new public declarations were axiom-audited once and use only `propext`, `Classical.choice` and `Quot.sound`. No numerical premise or proof placeholder is used.

Global `scripts/formal_tools.py lint` passed with existing large-file warnings only. The new leaf has no lint errors.
