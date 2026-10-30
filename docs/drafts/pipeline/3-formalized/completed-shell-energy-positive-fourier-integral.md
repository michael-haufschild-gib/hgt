# The completed shell energy is a positive Fourier integral

- **ID:** completed-shell-energy-positive-fourier-integral
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Q1 of `docs/reports/review-2910/obstacles-summary.md` (shell as a source); AGT §9
  "repayment of the nonpolar `−log c` losses by successor shells"; AGT question 7 (marginality);
  EAHT tools "signed symbol calculus for the completed shell operator on Ramanujan packets";
  RAPT `OverlapForcesNewRamanujanTerms` (continued reference energies become negative).
- **Statement:** For every `C²` profile `φ` supported in `[0,1]` with `M = ∫φ² > 0`, the
  completed conductor-one shell energy
  `E(c) = log(1/(2πc)) + β(φ)/M + c q − (2/M) Σ_{1≤h<c} ∫_{h/c}^1 G(u)/u du`
  (`G` the autocorrelation, `q = (∫φ)²/M`, `β` the Robin shape term) satisfies
  `E(c) = (2/M) Σ_{k≥1} (1/k) ∫_{kc}^∞ |φ̂(2πt)|² dt` for every `c > 0`.
  Hence `E ≥ 0`, `E` is antitone, `E(c) → 0`, and `E(c)` equals the actual limiting complete-Weil
  energy of the conductor-one Ramanujan mode for `0 < c < 1`.

## Paper proof

Notation. `φ̂(ξ) = ∫ φ(u) e^{iξu} du` (corpus `paperFT`), `P(ξ) = |φ̂(ξ)|²`, `G(x) = ∫ φ(u)φ(u+x) du`.
`G` is even, `C²`, `G(0) = M`, `G = 0` on `|x| ≥ 1`, `Ĝ = P` on `ℝ`, `∫G = P(0) = (∫φ)²`.
`β(φ) = ∫_0^1 ‖φ − φ(·+y)‖²/(2y) dy = ∫_0^1 (M − G(y))/y dy`.
`S(c) = Σ_{1≤h<c} ∫_{h/c}^1 G(u)/u du`, `E(c) = log(1/(2πc)) + β/M + cP(0)/M − 2S(c)/M`.

**1. Poisson at scale `s > 0`.** Poisson summation for the `C²` compactly supported `G` at lattice
`1/s` gives `Σ_{k∈ℤ} P(2πks) = (1/s) Σ_{m∈ℤ} G(m/s)`. Both `P` and `G` are even and `G(m/s) = 0`
for `|m| ≥ s`, so
`2 Σ_{k≥1} P(2πks) = M/s + (2/s) Σ_{1≤j<K} G(j/s) − P(0)` for every integer `K ≥ s`.

**2. Integration over `[c, C]`, `0 < c ≤ C`, `K = ⌈C⌉`.** The left side: `P ≥ 0` and
`P(ξ) ≤ N²/(1+|ξ|)⁴` make the series dominated on `[c,C]` by a summable constant sequence, so
`∫_c^C Σ_k = Σ_k ∫_c^C`, and `∫_c^C P(2πks) ds = (1/k) ∫_{kc}^{kC} P(2πt) dt`.
The right side: `∫_c^C ds/s = log(C/c)`; with `u = j/s`,
`∫_c^C G(j/s)/s ds = ∫_{j/C}^{j/c} G(u)/u du = ∫_{j/C}^1 G/u − ∫_{j/c}^1 G/u`,
and `∫_{j/c}^1 G/u = 0` when `j ≥ c` because `G = 0` on `[1, ∞)`. Summing over `1 ≤ j < K`
gives `S(C) − S(c)`. Dividing by `M`:

  `(2/M) Σ_{k≥1} (1/k) ∫_{kc}^{kC} P(2πt) dt = E(c) − E(C).`   (increment law)

**3. The limit.** By (increment law) `E` is antitone, so it suffices to take `C = n` integer.
For `u ∈ [0,1)`, `#{1 ≤ h < n : h ≤ nu} = ⌊nu⌋`, hence `S(n) = ∫_0^1 G(u)⌊nu⌋/u du` and, using
`nP(0) = 2n∫_0^1 G`,
`E(n) = log(1/(2πn)) + β/M + (2/M) ∫_0^1 G(u){nu}/u du`.
Write `G = M − (M − G)`:
- `∫_0^1 {nu}/u du = ∫_0^n {t}/t dt = n − n log n + log n!` (cells `[k,k+1]`:
  `∫_k^{k+1}(t−k)/t dt = 1 − k log((k+1)/k)`, telescoping). By Stirling
  `2 log n! = 2n log n − 2n + log(2πn) + o(1)`, so
  `log(1/(2πn)) + 2∫_0^1 {nu}/u du → 0`.
- `h(u) = (M − G(u))/u` extends continuously to `[0,1]` with `h(0) = −G′(0) = 0` (`G` even).
  For continuous `h`, `∫_0^1 h(u)({nu} − ½) du → 0` (uniform continuity on each cell
  `[j/n,(j+1)/n]`, where `{nu} − ½` has mean zero). Hence
  `(2/M)∫_0^1 (M − G){nu}/u → (1/M)∫_0^1 h = β/M`.
So `E(n) → β/M − β/M = 0`.

**4. Fourier representation.** Let `C → ∞` in (increment law): each `∫_{kc}^{kC} P(2πt) dt`
increases to `T(kc) = ∫_{kc}^∞ P(2πt) dt`, dominated by `T(kc) ≤ N²/(3(2π)^4(kc)³)`; dominated
convergence for series gives `E(c) = (2/M) Σ_{k≥1} T(kc)/k ≥ 0`.

**5. Below touching.** For `0 < c < 1`, `S(c) = 0` (empty shell range), so
`E(c) = completeWeilSelfFinitePart φ c + completeWeilPoleShift φ c
= completeWeilAdjunctionEnergy φ c 1`, the proved limit energy of the conductor-one mode.

## Meaning

- The shell correction `−2S(c)/M` is exactly what Poisson summation of the autocorrelation
  produces: the completed energy is the harmonic-number multiplier
  `(2/M)∫_0^∞ P(2πt) H_{⌊t/c⌋} dt`, `H_n = Σ_{k≤n} 1/k`. The uncompleted reference energy
  `log(1/(2πc)) + β/M + cq` grows linearly in `c` (pole charge); the shells take exactly this
  growth back and leave a positive, decreasing quantity.
- Marginality: `E(c) → 0` is Stirling's formula. The zero margin at infinite overlap is
  the matching of the archimedean finite part `−log 2π` with Stirling's constant.
- Identification of `E(c)`, `c ≥ 1`, with the actual matrix energy of the conductor-one mode is a
  separate theorem (next conjecture).

## Lean

Module: `formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheCompletedShellEnergyIsAPositiveFourierIntegral.lean`,
namespace `GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.CompletedShell`:

- `hasSum_completedShellEnergy_sub` — increment law (step 2);
- `completedShellEnergy_antitone`, `completedShellEnergy_nonneg`;
- `completedShellEnergy_natCast_succ` — exact Stirling form at integer overlap;
- `tendsto_completedShellEnergy_atTop` — `E(c) → 0`;
- `hasSum_completedShellEnergy` — positive Fourier representation (step 4);
- `completedShellEnergy_eq_adjunction` — `E = completeWeilAdjunctionEnergy φ c 1` for `0 < c ≤ 1`;
- `tendsto_cell_average` — cell averaging of a continuous function.

Checked with `lake --old env lean`; transitive axioms `propext`, `Classical.choice`, `Quot.sound`.
Wired into `RenormalizedArithmeticPotentialTheory.lean`.

## Log
- 2026-10-29 — card created; paper proof written.
- 2026-10-30 — formalized.
