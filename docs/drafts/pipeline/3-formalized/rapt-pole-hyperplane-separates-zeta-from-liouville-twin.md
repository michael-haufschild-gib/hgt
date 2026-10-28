# The pole hyperplane separates ζ from its Liouville twin

- **ID:** rapt-pole-hyperplane-separates-zeta-from-liouville-twin
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** RP29 (spectral gap below the pole); B3.16 (gauge form margin); the selective-positivity
  mechanism of `1-in-progress/selective-positivity-on-separated-atoms.md`.
- **Statement:** There is `g > 0` such that for every `ε > 0`, eventually in `N`: every `x` with
  `Σ_{n ≤ N} x_n/√n = 0` has `P_N(x) ≤ (log N − γ − g + ε)|x|²`, and some nonzero `x` with
  `Σ x_n/√n = 0` has `P_N(λx) ≥ (log N − γ − ε)|x|²` (`λ` Liouville).

## Proof

`ζ`: RP29. Twin: the witness `x = (λ − s) b`, `b_n = n^{−1/2}`, `s = S/H`, `S = Σ λ(n)/n`,
`H = Σ 1/n`, is the twin's top `λb` projected onto the pole hyperplane. Polarizing the ground-state
identity at the pole (the pole is in the kernel of the defect):
`P_N(b + u) = P_N(b) + P_N(u) + 2 Σ R_n b_n u_n`. With `u = −sλb`:
`P_N(λx) = P_N(b) + s² P_N(λb) − 2s Σ R_n λ(n)/n`. `P_N(b) ≥ (log N − γ − ε/2) H`;
`|P_N(λb)| ≤ (log N + log 4 + 4) H` (fixed-point law at `κ = −1`);
`|Σ R_n λ(n)/n| ≤ (log N + γ)|S| + B H` with `|R_n − (log N − γ)| ≤ B` (Mertens);
`|S| ≤ 2` from `Σ_{n ≤ N} λ(n)⌊N/n⌋ = #{squares ≤ N}`. Since `|s| ≤ 2/H`, all corrections are
`O(1)` while the target slack is `εH/2`.

## Significance

The prime forms of `ζ` and of its Liouville twin are unitarily equivalent (gauge `x ↦ λx`), so no
statement about the prime form alone separates them. Weil's pole term reads only `Σ x_n/√n`; on its
kernel the separation is a uniform margin `g`. This is the selective input "pole term" of the
gauge-principle reading, made quantitative: at atomic resolution the archimedean diagonal is gauge
blind, so the twin's form on the pole hyperplane sits `g` higher in the prime form than `ζ`'s.

## Status

Lean: `formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/ThePoleHyperplaneSeparatesZetaFromItsLiouvilleTwin.lean`
(`sum_divisors_liouvilleSign`, `sum_liouvilleSign_mul_div`, `abs_sum_liouvilleSign_div_le`,
`atomicWeilForm_smul`, `poleDefect_truncPole_add`, `atomicWeilForm_truncPole_add`, `abs_row_sub_le`,
`exists_pole_hyperplane_separates_liouville`). Axioms `propext, Classical.choice, Quot.sound`; wired.

Open: twins flipping a set of primes of logarithmic density `ϑ` (needs `Σ ε(n)/n = o(√log N)`,
true heuristically for `ϑ > 1/4`); transfer to Weil's form at the spacing with explicit constants.
