# The centred damping chain is Hilbert–Schmidt above damping (√5−1)/2

- **ID:** saei-chain-l2-golden
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** SAEI README §9 topic 4; improves `saei-chain-l2-root-two` (`η > 1/√2`)
- **Statement:** For `η² + η > 1` (`η > (√5−1)/2 ≈ 0.618`) the centred damping chain is
  Hilbert–Schmidt; hence bounded in `ℓ²` on finitely supported sequences.

## Goal
Measured progress on the unconditional `ℓ²` range of the receiver chain, from `1/√2` to the golden
threshold, by an elementary short-interval estimate for `c_η(m) = Σ_{d|m} μ(d) d^{−η}` that uses the
divisor structure (not the signs of `μ`). Source-pure; no zeros.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven: paper proof below, `[PROVED HERE]` after the audit of constants
- [ ] 2 → 3  formalized
- [ ] 3 → 4  n/a

## Approach — paper proof
**Short-interval lemma.** Let `0 < η < 1`, `a' < a`, `J = a − a'` with `2J ≤ a`, and `J ≤ D ≤ a`.
In floor form `P(a) − P(a') = Σ_{d ≤ a} μ(d) d^{−η}(n_d − J/d) − J·τ_a`, with
`n_d = ⌊a/d⌋ − ⌊a'/d⌋` (the multiples of `d` in `(a', a]`) and `τ_a = Σ_{d > a} μ(d) d^{−1−η}`.
- `d ≤ D`: `|n_d − J/d| ≤ 1`, so the part is `≤ Σ_{d ≤ D} d^{−η} ≲ D^{1−η}`.
- `d > D ≥ J`: `n_d ∈ {0,1}`, `Σ_{d>D} d^{−η} J/d ≲ J D^{−η}`; a divisor with `n_d = 1` has its
  multiple at `d e` with `e = ⌊a/d⌋ ≤ a/D`, and for fixed `e` such `d` lie in
  `((a − J)/e, a/e]`: at most `J/e + 1` of them, each with `d^{−η} ≤ (2e/a)^η`. So the part is
  `≤ Σ_{e ≤ a/D} (J/e + 1)(2e/a)^η ≲ J D^{−η} + a D^{−1−η}`.
- `J |τ_a| ≤ J a^{−η}/η ≤ J D^{−η}/η`.
Hence `|P(a) − P(a')| ≤ C_η (D^{1−η} + J D^{−η} + a D^{−1−η})`.

**Kernel sums.** As in `saei-chain-l2-root-two`, only the short-interval part of the kernel on
`K² ≤ N` needs care, with `a = ⌊N/K⌋ ≈ N/K`, `J ≤ 2N/K²`. Write `K = N^κ`.
- `K³ ≤ N` (`κ ≤ ⅓`): take `D = 2N/K²` (`≥ √a` there). The pieces give HS exponents
  `−2η + (2η−1)/3` and `(−1−4η)/3`, both `< −1` for `η > ½`.
- `K³ > N` (`⅓ < κ ≤ ½`): take `D = max(√a, 2N/K²)`; then
  `|ΔP| ≲ min(J, a^{(1−η)/2}) + J a^{−η/2}`. The last term has HS exponent `−η − (1+η)/3 < −1`.
  For the first, `min(J, X) ≤ J^λ X^{1−λ}` gives an exponent linear in `κ`; it is `< −1` on
  `[⅓, ½]` iff it is at both ends: `λ < (2η−1)/η` and `λ > (2−3η)/(1−η)`, compatible iff
  `η² + η > 1`.
The mean-value and fractional parts are HS for `η > ½` (already formalized).

## Log
- 2026-10-23 — created with the paper proof sketch; constants to be fixed during formalization.
