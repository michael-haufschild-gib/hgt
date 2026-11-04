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
  reflection. [N]
- **C2 (Perron).** For `0 < c < log 2` both sector ground states of the band are nonnegative. [N]
- **C3 (selection by stages).** The admissible `w_p` slice is `ℝ` at the entry of `p` and shrinks to
  a window of the order of the sector margins; the newest prime is the loosest. [N]
- **C4 (edge carries the newest prime).** Exact: `w_n |(f⋆f)(−log n)| ≤ (Λ(n)e^c/(2n)) levyEnergy f`;
  at entry the outward jumps carry the lag at ratio `w_n e^h/2`. Lean:
  `PrimeThreeEntry/TheWindowEdgeCarriesTheNewestPrime.lean`.

## No-go closure (mandatory when falsified)

## Log
- 2026-11-04 — created in 1-in-progress
