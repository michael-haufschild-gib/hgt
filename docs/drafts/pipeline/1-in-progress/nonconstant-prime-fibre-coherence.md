# Coherence in a nonconstant prime fibre

- **ID:** critical-rigidity-nonconstant-prime-fibre
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Question:** Does removing the generator's global pole output make its norm uniformly bounded relative to adjunction energy?

## Arithmetic candidate

Take normalized conductor packets supported on `2p`, with odd primes `p≤R`. The prime generator's downward divisor expansion predicts three orthogonal components:

`G F = (Σ_p log p / sqrt(p−1) · a_p)e_2`
`      + Σ_p log 2 · a_p e_p`
`      − Σ_p [log 2 + log p/(p−1)]a_p e_(2p)`.

Both input and output have zero constant mode. The parity row can nevertheless add coherently. Its exact squared norm relative to input adjunction is

`H_R=Σ_(3≤p≤R) (log p)² / [(p−1)(2 log 2+p log p/(p−1))]`.

The formal candidate is `H_R ≥ (1/3)Σ_(3≤p≤R)log p/p`; the elementary comparison uses `log 2≤log p`. If the literal source identity and this bound are proved, global pole removal cannot eliminate logarithmic amplification. A fixed nonconstant receiving conductor can carry it.

## Positive survivor sought

An exact decomposition by receiving conductor, retaining coherent sums along each prime divisor fibre. The prime-only sector isolates a rank-one pole interaction; composite fibres test whether the same mechanism recurs throughout the conductor lattice. A relative theory would then need to control these row interactions jointly, rather than remove a single global pole row.

## Inputs to establish

- Identify the actual generator on `2p` from the proved divisor-jet expansion.
- Prove orthogonality and exact adjunction energy of the packet.
- Prove the sharp parity-row constant and explicit extremizer.
- Transfer the prime Mertens lower growth to `H_R`.

No theorem, no-go closure, or complete-form obstruction is claimed yet. This concerns the prime generator alone; Gamma and shell cancellation remain possible.
