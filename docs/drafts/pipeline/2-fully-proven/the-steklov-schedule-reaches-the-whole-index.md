# The Steklov schedule reaches the whole index

- **ID:** the-steklov-schedule-reaches-the-whole-index
- **Stage:** 2-fully-proven
- **Statement:** For every `β>2`, the negative indices of the complete atomic Weil
  Gram matrices with profile `steklovDCProfile` and width
  `(log log N)(log log log N)^β/N` converge in `ℕ∞` to the index of the ζ Weil kernel.
- **Scope:** Full-index part of A4. Effective numerical horizons remain separate.

## Proof

Fix a finite `m` below the kernel index. Integer translates of the cubic spline
contain a finite Gram matrix with at least `m` negative eigenvalues. Mollifying
these tests by a sufficiently narrow Steklov profile preserves this inequality:
the common sup and Lévy errors vanish, so the Gram matrices converge entrywise
and negative index is lower semicontinuous.

The mollified tests have common compact support and derivative bounds
`M b^q q! (log(q+3))^(2q)`. This follows by differentiating the convolution,
bounding the spline factor by its supremum, and applying the profile's proved
`L¹` derivative bounds.

Write `κ_N=N/((log log N)(log log log N)^β)`. The existing growth theorem gives
`κ_N→∞` and
`(N/κ_N)/((log log κ_N)(log log log κ_N)^2)→∞`.
These limits persist after each fixed integer shift of the horizon.
For the Euler–Maclaurin synthesis on horizons `nB`, put
`p=2 ceil(log log κ)+2` and `r=p log²(p+3)(b+Bφκ+p)/n`.
The elementary bound

`r ≤ 24b log³(nB)/n + 144 log⁴(nB)/n + 24BφB / growthRate`

gives `r→0`. Eventually `r≤exp(-1)` and `p≥2 log log κ`, hence
`r^p≤(log κ)^(-2)`. The common synthesis error is bounded by
`MA/(log κ)^2 + M b W₁ A₀/κ`; it tends to zero, as does its square times
`log κ`. The existing Lipschitz estimate gives convergence of the Lipschitz
bound divided by `κ`, which makes the Lévy error tend to zero.

Consequently every residue class modulo the finite support block size eventually
carries the chosen `m` negative directions. Finitely many residue classes cover
all sufficiently large horizons. The universal receiver bound caps each atomic
index by the kernel index. These two bounds give convergence in `ℕ∞`, whether
the kernel index is finite or infinite.

## Inputs

`exists_spline_family`, `tendsto_weilGram_of_perturbation`,
`eventually_le_hermNegIndex_of_synthesis`, `hermNegIndex_atomicGram_le`,
`exists_dcLogSynthesis`, `integral_abs_iteratedDeriv_steklovDCProfile_le`,
and `overlapGrowthSuperGevrey_of_two_lt`.

## Verification

Lean formalization in progress.
