# The centred prime row passes the coherent-block obstruction below the quadratic horizon

- **ID:** prime-row-coherent-block-2026-10-21
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), one module
- **Source:** docs/reports/review-2110/walls-ledger.md (Wall 17 / coherent blocks: "replacement hypotheses proved sufficient: block equidistribution of the large-scale row at scale `H = o(P/log² P)`"); hard-obstacles-summary §2.2 O1 ("the replacement hypotheses … are themselves O1")
- **Statement:** For `7/12 < α < 1` and `0 < ε ≤ 1` there is `Q₀` such that for every window `[A, A + KH) ⊆ [Q, 2Q]` with `Q ≥ Q₀`, blocks of length `(2Q)^α ≤ H ≤ 4Q^α`, horizon `N ≥ 2Q`, and every row `c` on `(P, 2P]` with `H h_N²/2 + 1/8 ≤ εP` and `3P ≤ 2εQ`: the cross-scale remainder of `c` against the centred prime row `c'(n) = Λ(n) − 1` on the window satisfies `|B + mR' + βH'| ≤ 16 ε S₀ Σ_d |c(d)| d`, `S₀ = Σ_n |c'(n)|/n²`. The hypotheses hold throughout `P^{1+δ} ≤ Q ≤ P^{12/7−δ}`, i.e. at every cross-scale exponent `θ = 2 log P/log Q ∈ (7/6, 2)`.

## Goal
Wall 17 says no `ℓ²` coefficient class reaches a cross-scale exponent `θ > 1` on the pronic prime
Gram (coherent blocks attain the large-sieve loss), and names block equidistribution of the
large-scale row at scale `H = o(P/log² P)` as the replacement hypothesis, filed under
square-root-cancellation strength (O1). For the actual centred prime row that hypothesis is a
short-interval prime count, `ψ(a − 1 + H) − ψ(a − 1) − H = o(H)` at `H ≍ Q^α`, which Huxley's theorem
(`RHTower.tendsto_psi_short_window_div_seven_twelfths`, exponent `12/5` zero density) gives for
every `α > 7/12`. Since `Q^α (log Q)² ≤ P` whenever `Q ≤ P^{12/7 − δ}`, the whole obstructed regime
`Q < P^{5/3}` is covered: below the quadratic horizon the coherent blocks obstruct only sign-blind
classes, not the prime row. The replacement hypothesis is therefore not of O1 strength for the prime
row away from the balanced regime; what remains is `Q ≍ P`, where the cubic tail
`Σ_d |c(d)| d² Σ_n |c'(n)|/n³` is itself of rank-two size and no block argument applies.

Non-circular: zero-density input only (Huxley `12/5`), no RH. Selective: the statement is about the
actual von Mangoldt row; the shifted pair `ζ(s−a)ζ(s+a)` has coefficients `2Λ(n)cosh(a log n)` whose
centred short-interval sums are not `o(H)`.

## Gates
- [x] 0 → 1 well-posed, source-pure
- [x] 1 → 2 paper proof (Approach)
- [x] 2 → 3 Lean: `formal/GaloisForLFunctions/BezoutValuationIncidence/CentredPrimeRowPassesTheCoherentBlockObstruction.lean`, `lake env lean` clean (no warnings), olean built single-threaded, 8 declarations audited (`propext, Classical.choice, Quot.sound`), import inserted in `BezoutValuationIncidence.lean` before the trailing module docstring
- [ ] 3 → 4 not pursued

## Approach
1. **Huxley uniformly in the window length** (`eventually_abs_psi_window_sub_le`): the corpus's
   two-sided window bounds `psi_window_le_add_zeroShortWeight`, `psi_window_ge_sub_zeroShortWeight`
   hold for every `h` with parameters `c x²/(h·h/M)`; the weighted zero sums are monotone in the
   parameter, `c x²/(h·h/M) ≤ cM x^{2(1−α)}` for `h ≥ x^α`, and `Σ' zeroShortWeight x (8M x^{2(1−α)}) → 0`
   (`tendsto_tsum_zeroShortWeight_seven_twelfths`, `u = 1 − α < 5/12`). With `M ≥ 8/ε` and `x ≥ 16M/ε`
   all three error terms are `≤ εh/4`, so `|ψ(x+h) − ψ(x) − h| ≤ εh` for all `x^α ≤ h ≤ x/2`.
2. **One block** (`abs_sum_centredPrimeRow_block_le`): `Σ_{Ico a (a+H)} Λ = ψ(a−1+H) − ψ(a−1)`
   (`sum_Ico_vonMangoldt_eq_psi_sub`); split `(Λ−1)/n² = (Λ−1)/a² − (Λ−1)(1/a² − 1/n²)` with
   `0 ≤ 1/a² − 1/n² ≤ 2H/a³` (`inv_sq_sub_inv_sq_le`): `|block| ≤ εH/a² + 6H²/a³`.
3. **Mass** (`one_div_twelve_le_abs_vonMangoldt_sub_one`): `|Λ(n) − 1| ≥ 1/12` since `Λ ∈ {0, log 2} ∪ [log 3, ∞)`
   and `log 2 ≤ 11/12`, `log 3 ≥ 13/12` (`e^{13/12} ≤ 2.7182818286·12/11 < 3`); hence
   `S₀ ≥ KH/(48Q²)` (`mass_centredPrimeRow_ge`) and `Δ_H ≤ 2εKH/Q² ≤ 96εS₀`.
4. **Thresholds** (`exists_abs_rowBilinear_centredPrimeRow_le`): `Q₀` from the window theorem and
   `100/ε ≤ Q^{1−α}`, which gives `25H ≤ εQ`, hence `H ≤ (a−1)/2` and `6H/a ≤ ε` on every block
   (`abs_sum_block_le_of_window`). The three terms of `abs_rowBilinear_add_mean_add_beta_le_block`
   are bounded by `14εS₀Σ|c|d`, `εS₀Σ|c|d` (`P Σ|c| ≤ Σ|c|d`) and `εS₀Σ|c|d`
   (`Σ|c|d² ≤ 2PΣ|c|d`, `QΣ|c'|/n³ ≤ S₀`, `3P ≤ 2εQ`), assembled over plain reals (`assembly_le`).

## What it does not give
The balanced regime `Q ≍ P` (the receiver window `θ = 2`): there the term `3P/(2Q)` is not small and
the short-window saving for `Λ` at length `≍ Q/log³ Q` is only of zero-free-region strength. The
Möbius row: its block equidistribution at `Q^{7/12+ε}` needs Möbius in short intervals (Ramachandra),
not in the corpus; the almost-all (Matomäki–Radziwiłł) version is being built in
`ShortWindowMeanSquareCarriesTheCrossScaleLoss` / `MoebiusCancelsInAlmostAllLinearShortWindows`.

## Log
- 2026-10-21 — created in 3-formalized. Module compiled (`lake env lean`, no warnings), olean built
  single-threaded, axioms standard for all 8 checked declarations, wired. Lean lessons: identifiers
  containing `Σ` do not parse; a `set`-laden final theorem exceeded the default heartbeat budget and
  was split into `abs_sum_block_le_of_window`, named masses `rowInverseSquareMass`/`rowLinearWeight`,
  and a plain-real `assembly_le`; the BVI umbrella keeps its module docstring last, so imports are
  inserted before it rather than appended.
