# The Mellin integral representation is MATHLIB's, not ours (2026-08-07)

**`LSeries_eq_mul_integral` and `LSeries_eq_mul_integral'` are in mathlib**
(`Mathlib/NumberTheory/LSeries/SumCoeff.lean`):

`L(f,s) = s ∫_{Ioi 1} (∑_{k ∈ Icc 1 ⌊t⌋₊} f k) t^{-(s+1)}` whenever the partial sums are `O(n^r)` and
`r < Re s`. The zeta instance is the corpus's `RHTower.riemannZeta_eq_mul_integral_floor`
(`RHTower/FractionalPartZeta.lean`), which already calls the mathlib lemma.

I re-proved both from mathlib's Abel summation before finding them, and deleted the duplicates. The
only new content is `RHTower.Sieve.inv_riemannZeta_eq_mul_integral_mertens`:
`1/ζ(s) = s ∫ M(⌊t⌋) t^{-(s+1)}` for `Re s > 1`, three lines from `‖μ‖ ≤ 1` and
`RHTower.LSeries_moebius_eq_inv_riemannZeta` (`SquarefreeMoebiusNormalization`).

**The search that finds such things:** grep for the *conclusion shape* — `s * ∫ t in Ioi 1`,
`Icc 1 ⌊t⌋₊`, `=O[atTop] fun n => (n : ℝ) ^ r` — in `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/`
and in `GaloisForLFunctions/`. A `formal_tools.py research` query about the *concept*
("Mellin transform of a partial sum", "summatory function") finds nothing, because neither mathlib nor
the corpus names it that way. Same failure mode as the Halász recursion earlier the same day
(`sum_mul_log_eq_vonMangoldt` in Sieve/DivisorSwap).

Still useful to remember: the vertical kernel here is `1/s` (decay `1/|t|`), whereas every *smoothed*
Perron passage in the corpus carries a kernel that costs `∫‖W‖ ≍ N log N`.
