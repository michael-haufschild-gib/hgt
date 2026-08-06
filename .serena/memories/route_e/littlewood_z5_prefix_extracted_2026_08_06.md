# Littlewood Z5: prefix bound extracted, full σ block bound (2026-08-06)

Added to `formal/GaloisForLFunctions/RHTower/Sieve/DirichletBlockSigma.lean` — built, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

- `phase_prefix_bound (t) (ht) (k N M) (hk) (hN) (hNM) (hM) (hlam1)` :
  `∀ m ∈ [N,M], ‖∑_{Ico N m} n^{−It}‖ ≤ 256((M−N)X + (M−N)^{1−4/2^k} Y)`
  with `X = (4^k lam)^{1/(2^k−2)}`, `Y = lam^{−2/2^k}`, `lam = (t/2π)(k−1)!/(2N)^k`.
  **`dirichlet_block_one_full` proves exactly this inside its own proof, where it is not reusable.**
  Extracting it lets one derivative-test input serve any weight; the σ=1 case can be refactored onto
  it later.
- `dirichlet_block_sigma_full` : full block bound off the line — same bracket, `N^{−σ}` for `N^{−1}`.
  One-line proof: `dirichlet_block_sigma_bound` ∘ `phase_prefix_bound`.

## Confirmed structural claim

**The derivative-test half of the chain is entirely σ-independent.** The rectangle version differs
from the line version only in the weight of the final Abel step.

## Remaining for Z5

Re-run the assembly (saving → schedule → dyadic tail → head/tail split) with `N^{−σ}` for `N^{−1}`.
Same arguments throughout; only the harmonic head becomes `∑ n^{−σ}` and the block savings acquire
`N^{−σ}`.
