# High prime-power supports give exact horizon frames

- **Stage:** 1-in-progress.
- **Type:** CONJECTURE.
- **Wall:** Σ1e.
- **Statement:** Distinct prime-power conductors whose preceding powers exceed `sqrt N` have exactly orthogonal horizon vectors; through `m≤N^θ`, their lower frame constant is `1−θ`.

For primes `p`, choose exponents `k_p≥1`, put `d_p=p^(k_p−1)` and `m_p=p d_p`, and suppose `d_p d_q>N` for distinct primes. The identity

`c_(m_p)(n)=m_p 1_(m_p|n)−d_p 1_(d_p|n)`

makes different supports disjoint. The predicted exact diagonal is

`log N ‖v_(m_p,N)‖² = [(p−2)/(p−1)] H_floor(N/m_p) + [1/(p−1)] H_floor(N/d_p)`.

Both coefficients are nonnegative and sum to one. Thus `m_p≤N^θ`, `θ<1`, should give diagonal at least `(1−θ)log N`. For fixed `k≥3`, the nonempty range begins at `θ>k/(2(k−1))`.

Corpus leads: `TheRamanujanModesAreValuationSteps` supplies the prime-power identity; existing complete-period orthogonality and fixed-conductor limits do not assert this finite-horizon diagonalization. The prime-band disjoint-support theorem suggests the mechanism. Exact normalization, novelty, and Lean proof remain to be audited.
