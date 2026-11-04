# The pole does not decide the half-power law

- **ID:** F0311-Q4-5.4
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0311/fable.md` §5.4; loop card `1-in-progress/fable-0311-q4-breakthrough-questions.md`
- **Statement:** The flip points `x_θ` carry the pole of the trivial point and have Möbius exponent
  exactly `max(θ, Θ)`, unconditionally; for `θ > 1/2` they violate the Möbius half-power law. The
  pole-subtracted exponent of the prime source ranges over exactly `[Θ, 1]` on
  the gauge torus, minimized at the trivial point; RH iff the range is `[1/2, 1]`. For `0 < θ < 1` let `x_θ` be the gauge point with `χ(p) = −1` on the first
  `⌊4^{θk}⌋` primes of each octave `(4^k, 2·4^k]` and `χ(p) = 1` elsewhere. Then `x_θ` carries the
  pole of the trivial point up to `(N+1)^b` for every `b > θ` (so `ψ_{x_θ}(N)/N → 1`); below `θ` the
  points `0` and `x_θ` cannot both satisfy a pole-subtracted power law; above `θ` the law passes from
  `0` to `x_θ`; the pole-subtracted exponent of `x_θ` is exactly `θ` for every `θ` between the
  exponent `Θ_ψ` of `0` and `1` (under RH: every `θ ∈ (1/2, 1)`). Hence for `0 < b < 1`
  and `a < b` some gauge point shares the pole of `0` up to `(N+1)^b` and violates the law of
  exponent `a`.

## Answer to §5.4

§5.4 asks to prove the half-power law at `x = 0` from a property of the pole alone. This is
impossible, in both forms of the law. **Möbius form** (`GaugeHalfPowerLaw moebiusSource`): for
`1/2 < b < 1`, a property holding at every point that carries the pole of `0` up to `(N+1)^b` does not
imply the Möbius half-power law (`moebius_halfPowerLaw_not_decided_by_pole`), because the flip point
`x_θ`, `1/2 < θ < b`, carries that pole and has Möbius exponent `max(θ, Θ) ≥ θ > 1/2`
(`gaugeExponent_moebius_flipPoint`), unconditionally. **Prime-source form:** every property that holds at all gauge points carrying the pole of `0` up to precision
`N^b` (`b < 1`) fails to imply the pole-subtracted power law of any exponent `a < b`
(`no_pole_property_implies_powerLaw`). The flip points `x_θ` have the pole of `0` (same residue,
difference `O(N^θ log N)`) and, under RH, pole-subtracted exponent `θ` for every `θ ∈ (1/2, 1)`.
A proof of the half-power law at `0` must read the prime source to precision `N^{1/2+ε}` on sparse
prime sets of every exponent above `1/2`, which is the half-power law itself (RH,
`riemannHypothesis_iff_twistedPsi_zero_sub`). What the pole does decide is the shape of the whole
picture: the pole-subtracted exponent ranges over exactly `[Θ, 1]` on the gauge torus, the trivial
point is its minimizer (`poleSubtractedExponent_zero_le`), Haar-almost every point (no pole) sits at
`1`, and every intermediate value is a sparse flip of `0`. RH is the single statement that the
minimum is `1/2` (`riemannHypothesis_iff_range_poleSubtractedExponent`); the positive statement, the
half-power law at `0`, remains RH.

## Paper proof

Write `ψ_y(N) = Σ_{n≤N} Λ(n)χ_y(n)`, `S_θ = ⋃_k F_k` the flip primes.

1. **Charge identity.** `χ_{x_θ}(p^k) = (−1)^k` for `p ∈ S_θ` and `1` otherwise, real. Hence
   `ψ_0(N) − ψ_{x_θ}(N) = T_θ(N) := Σ_{n≤N} Λ(n)(1 − Re χ_{x_θ}(n))`, each term in `[0, 2Λ(n)]`.
2. **Upper bound.** Terms vanish unless `n = p^k` with `p ∈ S_θ`, `p ≤ N`. The powers of one prime
   `p` below `N` carry `Λ`-mass `⌊log_p N⌋ log p ≤ log N`. So `T_θ(N) ≤ 2 log N · #(S_θ ∩ [1, N])`.
   A flip prime `≤ N` lies in a block with `4^k < N`, `k ≤ log_4 N`; with `r = 4^θ`,
   `#(S_θ ∩ [1,N]) ≤ Σ_{k ≤ log_4 N} r^k ≤ r^{K}/(r−1) ≤ r/(r−1) · N^θ`.
3. **Same pole.** With `log N ≤ (N+1)^{b−θ}/(b−θ)`, `T_θ(N) ≤ C (N+1)^b` for every `b > θ`. For
   `b < 1`, `(ψ_{x_θ} − ψ_0)(N)/N → 0`, so `ψ_{x_θ}(N)/N → 1` by the prime number theorem.
4. **Lower bound.** The octave `(4^k, 2·4^k]` holds `≥ ½·4^k/log 4^k` primes for large `k` (prime
   number theorem), and `⌊4^{θk}⌋ ≤ 4^k/(2k log 4)` once `2k log 4 ≤ (4^{1−θ})^k`. So eventually
   `#F_k = ⌊4^{θk}⌋`, and `T_θ(2·4^k) ≥ Σ_{p∈F_k} 2 log p ≥ ⌊4^{θk}⌋ > 4^{θk} − 1`.
5. **Below `θ`.** If `‖ψ_0(N) − N‖, ‖ψ_{x_θ}(N) − N‖ ≤ C(N+1)^a` with `0 ≤ a < θ`, then
   `T_θ(N) ≤ 2C(N+1)^a`, and at `N = 2·4^k`: `4^{θk} < 1 + D·4^{ak}`, `D = 2C·3^a`. Since
   `(4^{θ−a})^k → ∞`, this fails for large `k`.
6. **Above `θ`.** `‖ψ_{x_θ}(N) − N‖ ≤ ‖ψ_0(N) − N‖ + T_θ(N)` and step 3.
7. **Under RH.** `|ψ(N) − N| ≤ C N^{1/2+ε}`, so `0` satisfies every law above `1/2`; steps 5–6 give the
   exponent `θ` for `x_θ`.
8. **Spectrum.** Let `E(y) = inf{a ≥ 0 : ‖ψ_y(N) − N‖ ≪ (N+1)^a}`; Chebyshev's bound makes the set
   nonempty at `0`. For `E(0) < θ < 1`: every `b > θ` has a law at `0` (some admissible `a < b`),
   which passes to `x_θ` (step 6), so `E(x_θ) ≤ θ`; a law at `x_θ` of exponent `a < θ`, raised to
   `a' = max(a, (E(0)+θ)/2) < θ`, would hold at both points, contradicting step 5. Under RH
   `E(0) ≤ 1/2`.
9. **The answer.** Given `0 < b < 1`, `a < b`: if `0` fails the law of exponent `a`, take `y = 0`;
   otherwise take `θ = (max(a, 0) + b)/2` and `y = x_θ` (steps 3, 5).

10. **The whole spectrum.** Coherence: `Re ψ_y(N) = Σ Λ(n) Re χ_y(n) ≤ ψ(N)`. A law of exponent `a`
    at `y` gives `ψ(N) − N ≥ −C(N+1)^a`. (i) Schmidt: `ψ(x) − x < −c√x` for arbitrarily large `x`;
    with `ψ(x) = ψ(⌊x⌋)` this forces `a ≥ 1/2`, so `E(y) ≥ 1/2`. (ii) For `a ≥ 1/2` each square
    sample has `ψ(s²) − s² ≥ −C 2^a N^{2a}` (`s < N`), so `Σ_{s<N}(ψ(s²) − s²) ≥ −C2^a N^{2+2(a−1/2)}`
    and the one-sided lower strip law gives `Θ ≤ a`; hence `E(y) ≥ Θ`. (iii) `|ψ(N) − N| ≪ N^{Θ+ε}`
    gives `E(0) = Θ`. (iv) `‖ψ_y(N) − N‖ ≤ ψ(N) + N ≤ (log 4 + 5)(N+1)` gives `E ≤ 1`. (v) At
    Haar-almost every `y`, `‖ψ_y(N)‖ ≪ √(N+1)(1 + log(N+1))³ ≤ 13³(N+1)^{3/4}`; a law of exponent
    `a < 1` would give `N ≤ K(N+1)^{max(a,3/4)}`, false. With step 8 the range of `E` is `[Θ, 1]`;
    RH iff `Θ = 1/2` iff the range is `[1/2, 1]`.

11. **Möbius exponent of `x_θ`.** Let `f = μχ`, `b = f * 1`: multiplicative with `b(p^k) = 1 − χ(p)`
    (`2` on flip primes, `0` elsewhere), so `b ≥ 0`. Euler product: `Σ_k b(p^k)p^{−kσ} =
    1 + c_p r/(1−r) ≤ exp(c_p r/(1−r))`, `r = p^{−σ}`, and `Σ_{p flip} p^{−σ} ≤ (1 − 4^{θ−σ})^{−1}`
    for `σ > θ`; hence `Σ b(n)n^{−σ} < ∞` for `σ > θ`, while full blocks give `Σ_{p ∈ F_k} p^{−θ} ≥
    2^{−θ}/2`, so `Σ_{p flip} p^{−θ} = ∞`. If `|Σ_{n≤N} f(n)| ≤ C(N+1)^a`, `a < θ`, then
    `D(s) = Σ f(n)n^{−s}` converges and is holomorphic on `Re s > c`, `a < c < θ` (Abel summation);
    on `Re s > 1`, `D = L(f)` and `ζD = L(b)`. Both sides are holomorphic on the connected open set
    `{θ < Re s < 1} ∪ {θ < Re s, Im s > 0} ∪ {Re s > 1}`, which avoids `s = 1`, so `ζ(σ)D(σ) = L(b)(σ)`
    for real `σ ∈ (θ, 1)`. As `σ ↓ θ`, the left side stays near `ζ(θ)D(θ)`, the right side exceeds
    `Σ_{p ∈ F} p^{−σ}` for any finite set `F` of flip primes: contradiction. So `θ_μ(x_θ) ≥ θ`. Sparse
    invariance of the exponent (both directions, `x_θ` and `0` agree off the flip primes) gives
    `θ_μ(x_θ) ≤ max(θ, Θ)` and `Θ ≤ max(θ, θ_μ(x_θ))`; with `θ_μ(0) = Θ`, `θ_μ(x_θ) = max(θ, Θ)`.

## Lean

`formal/GaloisForLFunctions/ArithmeticGaugeTheory/ThePoleDoesNotDecideTheHalfPowerLaw.lean`:
`PoleSubtractedPowerLaw`, `SharesPoleUpTo`, `flipSize`, `flipBlock`, `flipPrimes`, `flipPoint`,
`twist_flipPoint_of_mem`, `twist_flipPoint_of_notMem`, `twist_flipPoint_primePow`, `flipCharge`,
`twistedPsi_zero_sub_flipPoint`, `sum_vonMangoldt_base_le`, `flipCharge_le`,
`card_flipPrimesUpTo_le`, **`sharesPoleUpTo_flipPoint`**, **`tendsto_twistedPsi_flipPoint_div`**,
`eventually_card_flipBlock`, `card_flipBlock_le_flipCharge`,
**`not_poleSubtractedPowerLaw_flipPoint`**, **`poleSubtractedPowerLaw_flipPoint`**,
`poleSubtractedPowerLaw_zero_of_riemannHypothesis`, **`riemannHypothesis_flipPoint_exponent`**,
`poleSubtractedExponent`, `poleSubtractedPowerLaw_zero_one`, `poleSubtractedPowerLaw_zero_of_lt`,
**`poleSubtractedExponent_flipPoint`**, **`riemannHypothesis_poleSubtractedExponent_spectrum`**,
**`pole_does_not_decide_powerLaw`**, **`no_pole_property_implies_powerLaw`**.

`formal/GaloisForLFunctions/ArithmeticGaugeTheory/ThePoleSubtractedSpectrumIsAnInterval.lean`:
`re_twistedPsi_le`, `norm_twistedPsi_le`, `poleSubtractedPowerLaw_one`,
`poleSubtractedExponent_le_one`, `psi_sub_ge_of_bound`, **`half_le_poleSubtractedExponent`**,
`zetaZeroAbscissa_le_of_poleSubtractedPowerLaw`, **`zetaZeroAbscissa_le_poleSubtractedExponent`**,
**`poleSubtractedExponent_zero`**, **`poleSubtractedExponent_zero_le`**,
**`ae_poleSubtractedExponent_eq_one`**, **`range_poleSubtractedExponent`**,
**`riemannHypothesis_iff_poleSubtractedExponent_zero`**,
**`riemannHypothesis_iff_range_poleSubtractedExponent`**.

`formal/GaloisForLFunctions/ArithmeticGaugeTheory/TheFlipPointsBreakTheMoebiusHalfPowerLaw.lean`:
`twist_flipPoint_eq_ofReal_re`, `flipTwist`, `flipMoebius`, `flipDivisorSum`,
`flipDivisorSum_prime_pow`, `flipDivisorSum_eq_ofReal`, `sum_rpow_le_of_subset_flipPrimes`,
`exists_sum_flipPrimes_rpow_gt`, `flipDivisorTerm`, `flipDivisorSeries_summable`,
`LSeriesSummable_flipDivisorSum`, **`not_gaugePowerBound_moebius_flipPoint`**,
**`gaugeExponent_moebius_flipPoint`**, **`gaugeExponent_moebius_flipPoint_of_le`**,
**`not_gaugeHalfPowerLaw_moebius_flipPoint`**, `Ico_subset_range_gaugeExponent_moebius`,
`riemannHypothesis_Ico_subset_range_gaugeExponent_moebius`,
**`moebius_halfPowerLaw_not_decided_by_pole`**.

All three modules checked with `lake --old env lean` (no errors, no warnings); transitive axioms of
`pole_does_not_decide_powerLaw`, `no_pole_property_implies_powerLaw`,
`riemannHypothesis_flipPoint_exponent`, `tendsto_twistedPsi_flipPoint_div`,
`poleSubtractedExponent_flipPoint`, `riemannHypothesis_poleSubtractedExponent_spectrum`,
`range_poleSubtractedExponent`, `riemannHypothesis_iff_range_poleSubtractedExponent`,
`poleSubtractedExponent_zero_le`, `gaugeExponent_moebius_flipPoint`,
`gaugeExponent_moebius_flipPoint_of_le`, `moebius_halfPowerLaw_not_decided_by_pole`: `propext`,
`Classical.choice`, `Quot.sound`. Wired into `ArithmeticGaugeTheory.lean`.

## Log
- 2026-11-04 — paper proof and Lean formalization
