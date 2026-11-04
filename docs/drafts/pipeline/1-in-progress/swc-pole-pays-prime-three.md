# Does the pole pay the prime 3?

- **ID:** swc-pole-pays-prime-three
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-0411/obstacles-summary.md` §2.8 follow-up; `swc-signed-certificate-below-log-four`
- **Statement:** On windows `[−c, c]`, `½ log 3 < c ≤ ½ log 3 + 1/40` (prime 3 acts and is collar-unpaid,
  `exists_prime_three_collar_unpaid`), decide which resource pays the prime-3 coupling — the pole, the
  trivial-zero Hankel squares, or the archimedean edge energy — and prove the answer.

## Goal
Band form below `log 4` (`zetaWindowPositive_iff_two_three_markov_hankel`), half-window `f` on `[−c, 0]`,
`M = archForm f`, `C, S` cosh/sinh half-moments, `m_* = leftMoment f (−½)`, `μ_k = leftMoment f σ_k`,
`s_n = (f⋆f)(−log n)`:
- odd: `4S² ≤ M + m_*² + Σ_k μ_k² + w₂s₂ + w₃s₃`;
- even: `m_*² + Σ_k μ_k² + w₂s₂ + w₃s₃ ≤ M + 4C²`.
Answer either with an exact payment mechanism for the prime-3 term or with an obstruction plus survivor.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Approach
1. Numerics (scratch only): ground energies of both sectors, admissible `w₃`- and `w₂`-slices of
   `belowLogFourBandWeights c`, effect of the Hankel squares, location of extremals.
2. Structural facts about the prime-3 term on the entry windows (support on the collar sliver,
   mirror symmetry about `−½ log 3`), proved in Lean.
3. Conjecture loop on the payment law.

## Numerics [N] (scratch harness `band2.py`, Legendre basis on `[−c, 0]`, K = 22; reproduces the
corpus margins odd `1.50·10⁻⁵`, even `5.6·10⁻⁸` at `c = ½ log 3`)
- Budget at the sector extremals (`‖f‖ = 1`), `c = ½ log 3 + 1/40`:
  odd `M = −0.757`, `m_*² = 0.320`, `Σμ_k² = 0.261`, `w₂s₂ = 0.199`, `w₃s₃ = +3.8·10⁻⁵`, `4S² = 0.023`;
  even `M = −0.357`, `4C² = 1.319`, `m_*² = 0.283`, `Σμ_k² = 0.658`, `w₂s₂ = 0.020`, `w₃s₃ = 2.7·10⁻⁷`.
  The pole is a 3 % debt in the odd sector and the only payer in the even sector.
- Extremals of both sectors are nonnegative on `[−c, 0]`; the odd one vanishes at the centre, the
  even one at the collar `−c`; both are small on the prime-3 sliver.
- Admissible slices of `belowLogFourBandWeights c` (both sectors), `δ = 2c − log 3`:

  | `δ` | `w₃` slice | `w₂` slice |
  |---|---|---|
  | `0` | `ℝ` | `[0.490090, 0.490131]` |
  | `0.0054` | `[−1.743, 2.751]` | `[0.490096, 0.490130]` |
  | `0.0134` | `[−0.207, 1.239]` | |
  | `0.0214` | `[0.248, 0.880]` | `[0.490109, 0.490130]` |
  | `0.0314` | `[0.466, 0.728]` | |
  | `0.0500` | `[0.5885, 0.6540]` | `[0.490121, 0.4901295]` |

  `w₂ = 0.4901291`, `w₃ = 0.6342841`. The odd sector floors and the even sector caps both weights;
  the `w₂` cap sits `≈ 2·10⁻⁷` above `w₂` (even margin `10⁻⁸`).
- The prime `3` is necessary from `δ ≈ 0.0155` (`c ≈ 0.557`): the odd sector with `w₃ = 0` fails
  there. Treating the prime-3 term as a potential (`|s₃| ≤ ∫_I f²`) fails from `δ ≈ 0.012` (odd) and
  `δ ≈ 0.019` (even).
- Without the trivial-zero squares the odd sector fails from `c ≈ 0.26` on (inside the proved range).
- The prime `2` enters the same way (`δ₂ = 2c − log 2`): `w₂` slice `[−3.19, 3.46]` at `δ₂ = 0.005`,
  `[−0.98, 1.46]` at `0.02`, `[0.126, 0.642]` at `0.06`; it becomes necessary (odd sector with
  `w₂ = 0` fails) at `δ₂ ≈ 0.050` (`c ≈ 0.372`), the prime `3` at `δ₃ ≈ 0.0155`. The necessity
  width shrinks with the sector margins.

## Conjectures
- **C1 (signature, not potential).** On every window `c ∈ (½ log 3 + 0.006, log 2)` no certificate
  that replaces `w₃ s₃` by `±w₃ ∫_I f²` exists; the prime 3 must enter through the sign of the sliver
  reflection. [N] Explicit witness at `c₁ = 287/500 < ½ log 3 + 1/40`: `f(u) = (u − a)(b − u)(1 +
  11.88 u/c₁ + 19.05 (u/c₁)²)` on `[a, b] = [−c₁ + 1/400, −1/400]` gives
  `𝓗₀(f) − w₂s₂(f) + w₃∫_I f² − W(f) = 0.0301 ‖f‖²` (independent 30-digit quadrature): the prime-2
  term is a cost there (`s₂ < 0`) and the prime-3 term helps (`s₃ > 0`). Lean certification is the
  next step (scale of `TwoProfileRefutationBelowLogFour`).
- **C2 (Perron).** For `0 < c < log 2` both sector ground states of the band are nonnegative. [N]
- **C3 (selection by stages).** The admissible `w_p` slice is `ℝ` at the entry of `p` and shrinks to
  a window of the order of the sector margins; the newest prime is the loosest. [N]
- **C4 (edge carries the newest prime) — PROVED [L].** For `f` vanishing left of `−c`:
  `(f⋆f)(−ℓ) = ∫_I (f₊² − f₋²)` on the sliver `I = [−c, c − ℓ]`, `|(f⋆f)(−ℓ)| ≤ ∫_I f²`,
  `Ω(δ)∫_I f² ≤ levyEnergy f` with `Ω(δ) ≥ max(2e^{−δ/2}, (e^{−1/2}/2) log(1/δ))`; hence
  `w_n|(f⋆f)(−log n)| ≤ (Λ(n)e^c/(2n)) levyEnergy f`, at entry `≤ (w_n e^h/2) levyEnergy ≤ e^{h−1} levyEnergy`,
  and below `log 4` `w₂|s₂| + w₃|s₃| ≤ (log 2/2 + log 3/3) levyEnergy`.
  `PrimeThreeEntry/TheWindowEdgeCarriesTheNewestPrime.lean` (clean, axioms standard).
- **C5 (soft entry) — PROVED [L].** `belowLogFourBandWeights c = oddBandWeights c ∩ evenBandWeights c`
  (both convex; at the arithmetic weights each is its parity sector); for `2c ≤ log 3` both are
  cylinders in `w₃`; a sector band with Lévy margin `η` admits every `w₃'` with
  `|w₃' − w₃| ≤ η Ω(2c − log 3)`, in particular `≤ η (e^{−1/2}/2) log(1/(2c − log 3))`.
  `PrimeThreeEntry/TheNewestPrimeEntersSoftly.lean` (clean, axioms standard).

- **C6 (confinement) — Lean pending.** For `½ log 3 < c < log 2`, `belowLogFourBandWeights c` is
  compact and convex: one bump centred at `−½ log n` (symmetric under the sliver reflection, so
  `(f⋆f)(−log n) = ∫ f² > 0`, and missing the other prime's reflection) pins `w_n` from both sides.
  `PrimeThreeEntry/TheWindowConfinesThePrimeWeights.lean`.

## Answer
- The pole does not pay the prime 3. At its entry the prime-3 coupling is carried locally by the
  window's outward edge jumps (C4, exact; ratio `w₃e^h/2`, against `2w₃e^h > 1` for the inside
  collar jumps of `TheCollarRatioIsSharp`), but no certificate can spend that edge energy: the
  sliver-potential certificate is false on every window `c ≥ 287/500` (C1, Lean pending). The
  prime 3 must enter through the sign of its reflection; in the odd sector it is a necessary payer
  from `c ≈ 0.557` [N].
- Budgets [N]: even sector — the pole `4C²` is the only payer; odd sector — the pole is a 3 % debt,
  the archimedean cross-Hankel (Gamma-pole mode + trivial zeros) and the prime 2 pay.
- The binding constraint below `log 4` is the even sector's cap on `w₂` (`2·10⁻⁷` above `Λ(2)/√2`
  at `c = ½ log 3 + 1/40`) [N]: pole credit against the prime 2, not the prime 3.

## No-go closure (mandatory when falsified)
- **Exact killing mechanism:** the sliver-potential certificate (prime-3 kick bounded by its
  collar mass) fails on an explicit odd test on every window `c ≥ 287/500` (C1).
- **Strongest positive survivor:** the signature law and the edge carrying law (C4, Lean), soft
  entry (C5, Lean), confinement (C6).
- **New insight:** local resources for the newest prime exist (the window edge carries it at ratio
  `< 1`), so the obstruction to collar-local payment is criticality (no slack), not locality.

## Log
- 2026-11-04 — created in 1-in-progress
