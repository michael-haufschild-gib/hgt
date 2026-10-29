# Seventy percent or a simple near-line off-line core

- **ID:** review-2910-w13-seventy-percent-near-line
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** [W13](../../../reports/review-2910/obstacles-summary.md)
- **Statement:** For every A>0 and ε>0, eventually in dyadic windows either N₀≥7N/10 or at least
  `(HD(1)−2/5−1/A−ε)N` simple off-line zeros have displacement at most A/log T.

## Paper proof

[PROVED HERE, pending Lean audit] Write S for simple off-line zeros and M for off-line multiple
mass. Existing unconditional census gives `S+2M≤(1−HD(1)+ε)N`; the exact partition is
`N=N₀+S+M`. Subtracting the census from twice the partition yields
`S≥(1+HD(1)−ε)N−2N₀`. Thus failure of `N₀≥θN` forces
`S≥(1+HD(1)−2θ−ε)N`, for any real θ. Existing displacement-moment control bounds the mass
farther than A/log T by N/A. The simple near count is at least S minus that far mass, proving
the general threshold law. At θ=7/10 its coefficient is `HD(1)−2/5−1/A−ε`.

This is a dichotomy and a conditional location statement about the actual zeros, not a 70% census.
The forced off-line fraction tends to `HD(1)−0.4` as A grows and ε decreases.

## Verification

- [x] Read existing multiplicity census and near/far partition; no extra zero-density assumption.
- [ ] General threshold and 70% specialization formalized and directly checked.
- [ ] Transitive axioms standard only; umbrella import wired.
